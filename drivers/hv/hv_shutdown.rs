//! Implementation of the shutdown utility.
use kernel::macros::pin_data;
use kernel::hv::{self, icmsg_hdr, util, PacketType, BUSPIPE_HDR_SIZE, ICMSG_HDR};
use kernel::{prelude::*, workqueue};
use kernel::sync::Arc;
use kernel::workqueue::{Work, WorkItem};
use kernel::{bindings, types::FromByteSlice, new_work, impl_has_work};
use core::mem::offset_of;

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

const BUF_SIZE: usize = 256;
const SHUTDOWN_WORK_ID: u64 = 1;
const REBOOT_WORK_ID: u64 = 2;
const HIBERNATE_WORK_ID: u64 = 3;

#[pin_data]
struct Shutdown {
    version: Option<i32>,
    buf: [u8; BUF_SIZE],
    #[pin]
    shutdown_work: Work<Shutdown, SHUTDOWN_WORK_ID>,
    #[pin]
    reboot_work: Work<Shutdown, REBOOT_WORK_ID>,
    #[pin]
    hibernate_work: Work<Shutdown, HIBERNATE_WORK_ID>,
}

impl_has_work! {
    impl HasWork<Self, SHUTDOWN_WORK_ID> for Shutdown { self.shutdown_work }
    impl HasWork<Self, REBOOT_WORK_ID> for Shutdown { self.reboot_work }
    impl HasWork<Self, HIBERNATE_WORK_ID> for Shutdown { self.hibernate_work }
}

impl WorkItem<SHUTDOWN_WORK_ID> for Shutdown {
    type Pointer = Arc<Shutdown>;
    fn run(ctx: Arc<Shutdown>) {
        pr_info!("Shutdown work run!");
    }
}
impl WorkItem<REBOOT_WORK_ID> for Shutdown {
    type Pointer = Arc<Shutdown>;
    fn run(ctx: Arc<Shutdown>) {
        pr_info!("Reboot work run!");
    }
}
impl WorkItem<HIBERNATE_WORK_ID> for Shutdown {
    type Pointer = Arc<Shutdown>;
    fn run(ctx: Arc<Shutdown>) {
        pr_info!("Hibernate work run!");
    }
}

impl util::Service for Shutdown {
    type Data = Arc<Self>;

    kernel::define_vmbus_single_id!("0e0b6031-5213-4934-818b-38d90ced39db");

    fn init() -> Result<Self::Data> {
        pr_info!("Rust: init shutdown service");
        let res = Arc::pin_init(pin_init!(Self {
            version: None,
            buf: [0; BUF_SIZE],
            shutdown_work <- new_work!(),
            reboot_work <- new_work!(),
            hibernate_work <- new_work!(),
        }))?;
        // TODO: check if hibernate is supported
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
                }

                bindings::ICMSGTYPE_SHUTDOWN => {
                    if let Some(flags) =u32::from_bytes_mut(buf,
                                                            ICMSG_HDR + offset_of!(bindings::shutdown_msg_data, flags)) {
                        match flags {
                            0..=1 => {
                                pr_info!("Shutdown request recieved successfully");
                                icmsghdrp.status = bindings::HV_S_OK;
                                workqueue::system().enqueue::<Self::Data, SHUTDOWN_WORK_ID>(data.into());
                            }
                            2..=3 => {
                                pr_info!("Restart request recieved successfully");
                                icmsghdrp.status = bindings::HV_S_OK;
                                workqueue::system().enqueue::<Self::Data, REBOOT_WORK_ID>(data.into());
                            }
                            4..=5 => {
                                pr_info!("Hibernate request recieved successfully");
                                icmsghdrp.status = bindings::HV_S_OK;
                                workqueue::system().enqueue::<Self::Data, HIBERNATE_WORK_ID>(data.into());
                            }
                            _ => {
                                pr_err!("Invalid shutdown request");
                            }
                        }
                    } else {
                        pr_err!(
                            "Invalid shutdown msg data, length too small: {}\n",
                            recvlen
                        );
                    }
                }

                _ => {
                    icmsghdrp.status = bindings::HV_E_FAIL;
                    pr_err!(
                        "Shutdown request received. Invalid msg type: {}\n",
                        msgtype
                    );
                }
            }

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
