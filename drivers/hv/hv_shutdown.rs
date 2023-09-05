//! Implementation of the shutdown utility.
use kernel::macros::pin_data;
use kernel::hv::{self, icmsg_hdr, util, PacketType, BUSPIPE_HDR_SIZE, ICMSG_HDR};
use kernel::{prelude::*, workqueue};
use kernel::sync::Arc;
use kernel::workqueue::{Work, WorkItem};
use kernel::{bindings, types::FromByteSlice, new_work, impl_has_work};
use core::convert::Infallible;
use core::mem::{offset_of, size_of};

const SD_MAJOR: i32 = 3;
const SD_MINOR: i32 = 0;
const SD_MINOR_1: i32 = 1;
const SD_MINOR_2: i32 = 2;
const SD_VERSION_3_1: i32 = SD_MAJOR << 16 | SD_MINOR_1;
const SD_VERSION_3_2: i32 = SD_MAJOR << 16 | SD_MINOR_2;
const SD_VERSION: i32 = SD_MAJOR << 16 | SD_MINOR;

const SD_MAJOR_1: i32 = 1;
const SD_VERSION_1: i32 = SD_MAJOR_1 << 16 | SD_MINOR;

const SD_VERSIONS: &[i32] = &[
    SD_VERSION_3_2,
    SD_VERSION_3_1,
    SD_VERSION,
    SD_VERSION_1
];

const BUF_SIZE: usize = (size_of::<bindings::shutdown_msg_data>() + ICMSG_HDR) * 2;
const SD_WK_ID: u64 = 1;
const RB_WK_ID: u64 = 2;
const HB_WK_ID: u64 = 3;

struct Shutdown {
    version: Option<i32>,
    buf: [u8; BUF_SIZE],
    work: Arc<SdWork>,
    hibernate_supported: bool,
}

#[pin_data]
struct SdWork {
    #[pin]
    shutdown_work: Work<SdWork, SD_WK_ID>,
    #[pin]
    reboot_work: Work<SdWork, RB_WK_ID>,
    #[pin]
    hibernate_work: Work<SdWork, HB_WK_ID>,
}


impl_has_work! {
    impl HasWork<Self, SD_WK_ID> for SdWork { self.shutdown_work }
    impl HasWork<Self, RB_WK_ID> for SdWork { self.reboot_work }
    impl HasWork<Self, HB_WK_ID> for SdWork { self.hibernate_work }
}

impl WorkItem<SD_WK_ID> for SdWork {
    type Pointer = Arc<SdWork>;
    fn run(ctx: Arc<SdWork>) {
        pr_info!("SdWork work run!");
        unsafe { bindings::orderly_poweroff(true); }
    }
}
impl WorkItem<RB_WK_ID> for SdWork {
    type Pointer = Arc<SdWork>;
    fn run(ctx: Arc<SdWork>) {
        pr_info!("Reboot work run!");
        unsafe { bindings::orderly_reboot(); }
    }
}
impl WorkItem<HB_WK_ID> for SdWork {
    type Pointer = Arc<SdWork>;
    fn run(ctx: Arc<SdWork>) {
        pr_err!("Hibernation is not currently supported in the rust driver");
    }
}

impl util::Service for Shutdown {
    type Data = Box<Self>;

    kernel::define_vmbus_single_id!("0e0b6031-5213-4934-818b-38d90ced39db");

    fn init() -> Result<Self::Data> {
        pr_info!("Rust: init shutdown service");
        // Infalliable because `?` will return instead of initializing
        let res = Box::init::<Infallible>(Self {
            version: None,
            buf: [0; BUF_SIZE],
            work: Arc::pin_init(pin_init!(SdWork {
                shutdown_work <- new_work!("SdWork::shutdown_work"),
                reboot_work <- new_work!("SdWork::reboot_work"),
                hibernate_work <- new_work!("SdWork::hibernate_work"),
            }))?,
            // SAFETY: C function does not impose any restrictions
            hibernate_supported: unsafe { bindings::hv_is_hibernation_supported() },
        })?;

        // This driver does not support hibernation
        res.hibernate_supported = false;

        if res.hibernate_supported {
            pr_info!("Hibernation supported");
        } else {
            pr_info!("Hibernation not supported");
        }
        Ok(res)

    }

    fn callback(data: <Self::Data as kernel::types::ForeignOwnable>::BorrowedMut<'_>, chan: &hv::Channel) {
        loop {
            let (requestid, recvlen) = if let Ok(ret) = chan.recv_packet(&mut data.buf) {
                ret
            } else {
                pr_err!("Shutdown request received. Could not read into sd txf buf\n");
                return;
            };

            if recvlen == 0 {
                break;
            }

            let buf = &mut data.buf[..recvlen];
            let icmsghdrp = if let Some(v) = icmsg_hdr::from_bytes_mut(buf, BUSPIPE_HDR_SIZE) {
                v
            } else {
                pr_err!(
                    "Shutdown request received. Packet length too small: {}\n",
                    recvlen
                );
                break;
            };

            icmsghdrp.icflags =
                (bindings::ICMSGHDRFLAG_TRANSACTION | bindings::ICMSGHDRFLAG_RESPONSE) as u8;

            let msgtype = icmsghdrp.icmsgtype as u32;
            let mut new_status: u32;
            match msgtype {
                bindings::ICMSGTYPE_NEGOTIATE => {
                    let ret = hv::vmbus::prep_negotiate_resp(buf, util::FW_VERSIONS, SD_VERSIONS);
                    if let Some((_, srv_version)) = ret {
                        pr_info!(
                            "Shutdown IC version {}.{}\n",
                            srv_version >> 16,
                            srv_version & 0xFFFF
                        );
                        data.version = Some(srv_version);
                    }
                    new_status = bindings::HV_S_OK;
                }

                bindings::ICMSGTYPE_SHUTDOWN => {
                    if let Some(flags) = u32::from_bytes(buf,
                                                         ICMSG_HDR + offset_of!(bindings::shutdown_msg_data, flags)) {
                        match flags {
                            0..=1 => {
                                pr_info!("Shutdown request recieved successfully");
                                new_status = bindings::HV_S_OK;
                                if let Err(_) = workqueue::system().enqueue::<Arc<SdWork>, SD_WK_ID>(data.work.clone()) {
                                    new_status = bindings::HV_E_FAIL;
                                    pr_err!("Failed to enqueue shutdown work");
                                }
                            }
                            2..=3 => {
                                pr_info!("Restart request recieved successfully");
                                new_status = bindings::HV_S_OK;
                                if let Err(_) = workqueue::system().enqueue::<Arc<SdWork>, RB_WK_ID>(data.work.clone()) {
                                    new_status = bindings::HV_E_FAIL;
                                    pr_err!("Failed to enqueue reboot work");
                                }
                            }
                            4..=5 => {
                                pr_info!("Hibernate request recieved successfully");
                                new_status = if data.hibernate_supported {
                                    if let Err(_) =
                                            workqueue::system().enqueue::<Arc<SdWork>, HB_WK_ID>(data.work.clone()) {
                                        pr_err!("Failed to enqueue hibernate work");
                                        bindings::HV_E_FAIL
                                    } else {
                                        bindings::HV_S_OK
                                    }
                                } else {
                                    bindings::HV_E_FAIL
                                };
                            }
                            _ => {
                                pr_err!("Invalid shutdown request");
                                new_status = bindings::HV_E_FAIL;
                            }
                        }
                    } else {
                        pr_err!(
                            "Invalid shutdown msg data, length too small: {}\n",
                            recvlen
                        );
                        break;
                    }
                }

                _ => {
                    new_status = bindings::HV_E_FAIL;
                    pr_err!(
                        "Shutdown request received. Invalid msg type: {}\n",
                        msgtype
                    );
                }
            }
            // Unwrap is ok, we've already checked that buf is big enough
            icmsg_hdr::from_bytes_mut(buf, BUSPIPE_HDR_SIZE).unwrap().status = new_status;

            let _ = chan.send_packet(buf, requestid, PacketType::DataInband);
        }
    }
}

kernel::module_vmbus_util_driver! {
    type: Shutdown,
    name: "hv_shutdown",
    author: "Mitchell Levy <levymitchell0@gmail.com>",
    license: "GPL",
}
