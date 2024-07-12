// SPDX-License-Identifier: GPL-2.0

//! vmbus devices and drivers.
//!
//! C header: [`include/linux/hyperv.h`](../../../../include/linux/hyperv.h)

//#[macro_use]
use crate::{
    bindings, device, driver,
    error::to_result,
    error::Result,
    str::CStr,
    types::ForeignOwnable,
    ThisModule,
};

use core::mem::offset_of;
use super::Vec;
use kernel::prelude::*;
/// A registration of a vmbus driver.
pub type Registration<T> = driver::Registration<Adapter<T>>;

/// Id of a vmbus device.
#[derive(Clone, Copy)]
pub struct DeviceId {
    /// GUID that identifies the device.
    pub guid: [u8; 16],
}

// SAFETY: `ZERO` is all zeroed-out, `to_rawid` stores `offset` in `hv_vmbus_device_id::driver_data`
// and `offset_from_rawid` retrieves it from the same field.
unsafe impl const driver::RawDeviceId for DeviceId {
    type RawType = bindings::hv_vmbus_device_id;
    const ZERO: Self::RawType = bindings::hv_vmbus_device_id {
        guid: bindings::guid_t { b: [0u8; 16] },
        driver_data: 0,
    };

    fn to_rawid(&self, offset: isize) -> Self::RawType {
        bindings::hv_vmbus_device_id {
            guid: bindings::guid_t { b: self.guid },
            driver_data: offset as _,
        }
    }

    fn offset_from_rawid(id: &bindings::hv_vmbus_device_id) -> isize {
        id.driver_data as _
    }
}

/// A vmbus driver.
pub trait Driver {
    /// Data stored on device by driver.
    type Data: ForeignOwnable + Send + Sync + driver::DeviceRemoval = ();

    /// The type holding information about each device id supported by the driver.
    type IdInfo: 'static = ();

    /// The table of device ids supported by the driver.
    const ID_TABLE: Option<driver::IdTable<'static, DeviceId, Self::IdInfo>> = None;

    /// Probes for the device with the given id.
    fn probe(
        dev: &mut Device,
        chan: super::ChannelToOpen,
        id_info: Option<&Self::IdInfo>,
    ) -> Result<Self::Data>;

    /// Cleans any resources up that are associated with the device.
    ///
    /// This is called when the driver is detached from the device.
    fn remove(_data: &mut Self::Data) -> Result {
        Ok(())
    }

    /// Prepares the device for suspension.
    fn suspend(_data: <Self::Data as ForeignOwnable>::BorrowedMut<'_>) -> Result {
        Ok(())
    }

    /// Prepares the device to resume from suspension.
    fn resume(_data: <Self::Data as ForeignOwnable>::BorrowedMut<'_>) -> Result {
        Ok(())
    }
}

/// An adapter for the registration of vmbus drivers.
pub struct Adapter<T: Driver>(T);

impl<T: Driver> driver::DriverOps for Adapter<T> {
    type RegType = bindings::hv_driver;

    unsafe fn register(
        reg: *mut bindings::hv_driver,
        name: &'static CStr,
        module: &'static ThisModule,
    ) -> Result {
        // SAFETY: By the safety requirements of this function (defined in the trait definition),
        // `reg` is non-null and valid.
        let drv = unsafe { &mut *reg };

        drv.name = name.as_char_ptr();
        drv.probe = Some(Self::probe_callback);
        drv.remove = Some(Self::remove_callback);
        drv.suspend = Some(Self::suspend_callback);
        drv.resume = Some(Self::resume_callback);
        if let Some(t) = T::ID_TABLE {
            drv.id_table = t.as_ref();
        }
        pr_info!("t-megha A driver is being registered -> {:?}", drv.name);
        // SAFETY:
        //   - `drv` lives at least until the call to `vmbus_driver_unregister()` returns.
        //   - `name` pointer has static lifetime.
        //   - `module.0` lives at least as long as the module.
        //   - `probe()` and `remove()` are static functions.
        //   - `T::ID_TABLE` is either a raw pointer with static lifetime,
        //      as guaranteed by the `driver::IdTable` type, or null.
        to_result(unsafe {
            bindings::__vmbus_driver_register(reg, module.0, module.name().as_char_ptr())
        })
    }

    unsafe fn unregister(reg: *mut bindings::hv_driver) {
        // SAFETY: By the safety requirements of this function (defined in the trait definition),
        // `reg` was passed (and updated) by a previous successful call to
        // `vmbus_driver_register`.
        unsafe { bindings::vmbus_driver_unregister(reg) };
    }
}

impl<T: Driver> Adapter<T> {
    fn get_id_info(id: *const bindings::hv_vmbus_device_id) -> Option<&'static T::IdInfo> {
        let table = T::ID_TABLE?;
        table.context_data(id)
    }

    extern "C" fn probe_callback(
        pdev: *mut bindings::hv_device,
        id: *const bindings::hv_vmbus_device_id,
    ) -> core::ffi::c_int {
        crate::error::from_result(|| {
            // SAFETY: `pdev` is valid by the contract with the C code. `dev` is alive only for the
            // duration of this call, so it is guaranteed to remain alive for the lifetime of
            // `pdev`.
            let mut dev = unsafe { Device::from_ptr(pdev) };
            let info = Self::get_id_info(id);
            // SAFETY: `pdev` is valid and the channel stored in it also valid and not opened yet,
            // these are guaranteed by the contract with the C code.
            let chan = unsafe { super::ChannelToOpen::new((*pdev).channel) };
            let data = T::probe(&mut dev, chan, info)?;
            // SAFETY: `pdev` is guaranteed to be a valid, non-null pointer.
            unsafe { bindings::hv_set_drvdata(pdev, data.into_foreign() as _) };
            Ok(0)
        })
    }

    extern "C" fn remove_callback(dev: *mut bindings::hv_device) {
        // SAFETY: `dev` is guaranteed to be a valid, non-null pointer.
        let ptr = unsafe { bindings::hv_get_drvdata(dev) };
        // SAFETY:
        //   - we allocated this pointer using `T::Data::into_foreign`,
        //     so it is safe to turn back into a `T::Data`.
        //   - the allocation happened in `probe`, no-one freed the memory,
        //     `remove` is the canonical kernel location to free driver data. so OK
        //     to convert the pointer back to a Rust structure here.
        let mut data = unsafe { T::Data::from_foreign(ptr) };
        let ret = T::remove(&mut data);
        <T::Data as driver::DeviceRemoval>::device_remove(&data);
        ret.expect("device removal failed");
    }

    extern "C" fn suspend_callback(dev: *mut bindings::hv_device) -> core::ffi::c_int {
        crate::error::from_result(|| {
            // SAFETY: `dev` is guaranteed to be a valid, non-null pointer.
            let ptr = unsafe { bindings::hv_get_drvdata(dev) };
            // SAFETY: `ptr` was initialised in `probe_callback` with the result of `into_foreign`,
            // and while `suspend` is being called, no other concurrent functions are called.
            let data = unsafe { T::Data::borrow_mut(ptr) };
            T::suspend(data)?;
            Ok(0)
        })
    }

    extern "C" fn resume_callback(dev: *mut bindings::hv_device) -> core::ffi::c_int {
        crate::error::from_result(|| {
            // SAFETY: `dev` is guaranteed to be a valid, non-null pointer.
            let ptr = unsafe { bindings::hv_get_drvdata(dev) };
            // SAFETY: `ptr` was initialised in `probe_callback` with the result of `into_foreign`,
            // and while `resume` is being called, no other concurrent functions are called.
            let data = unsafe { T::Data::borrow_mut(ptr) };
            T::resume(data)?;
            Ok(0)
        })
    }
}

/// A vmbus device.
///
/// # Invariants
///
/// The field `ptr` is non-null and valid for the lifetime of the object.
pub struct Device {
    ptr: *mut bindings::hv_device,
}

impl Device {
    /// Creates a new device from the given pointer.
    ///
    /// # Safety
    ///
    /// `ptr` must be non-null and valid. It must remain valid for the lifetime of the returned
    /// instance.
    unsafe fn from_ptr(ptr: *mut bindings::hv_device) -> Self {
        // INVARIANT: The safety requirements of the function ensure the lifetime invariant.
        Self { ptr }
    }
}

// SAFETY: The device returned by `raw_device` is the raw vmbus device.
unsafe impl device::RawDevice for Device {
    fn raw_device(&self) -> *mut bindings::device {
        // SAFETY: By the type invariants, we know that `self.ptr` is non-null and valid.
        unsafe { &mut (*self.ptr).device }
    }
}

/// Calculates the ring size for a payload of the given size.
pub fn ring_size(payload_size: usize) -> usize {
    unsafe { bindings::VMBUS_RING_SIZE(payload_size) }
}

pub struct icmsg_negotiate_rust {
    icframe_vercnt: u16,
    icmsg_vercnt: u16,
    reserved: u32
}

pub fn icmsg_negotiate_pkt_size(icframe_vercnt: usize, icmsg_vercnt: usize) -> usize {
    let sizeof_icmsg_negotiate = core::mem::size_of::<bindings::icmsg_negotiate>() as usize;
    let sizeof_ic_version = core::mem::size_of::<bindings::ic_version>() as usize;
    (super::ICMSG_HDR + sizeof_icmsg_negotiate) + (((icframe_vercnt) + (icmsg_vercnt)) * sizeof_ic_version)
}

/// Creates a response for a `negotiate` resquest.
///
/// `fw_versions` is a slice containing all supported framework versions.
/// `srv_versions`is a slice containing all supported service versions.
///
/// On success, returns the pair of negotiated framework and service versions, and updates `buf`
/// to hold the response.


fn resp_fw_srv_version(negop: &mut bindings::icmsg_negotiate,
                       ic_version_data: &mut Vec<bindings::ic_version>,
                           nego_fw_version: &mut i32,
                           nego_srv_version: &mut i32,
                           icframe_major: u16,
                           icframe_minor: u16,
                           icmsg_major: u16,
                           icmsg_minor: u16,
                           found_match: bool) -> bool {
        unsafe {
            if !found_match {
                negop.icframe_vercnt = 0;
                negop.icmsg_vercnt = 0;
            }
            else {
                negop.icframe_vercnt = 1;
                negop.icmsg_vercnt = 1;
            }
        
            pr_info!("t-megha response working.");

            *nego_fw_version = ((icframe_major as i32) << 16) | (icframe_minor as i32);
            *nego_srv_version = ((icmsg_major as i32) << 16) | (icmsg_minor as i32);

            /*
            if nego_fw_version.is_null() == false {
                *nego_fw_version = ((icframe_major as u32) << 16) | (icframe_minor as u32);
            }
        
            if nego_srv_version.is_null() == false {
                *nego_srv_version = ((icmsg_major as u32) << 16) | (icmsg_minor as u32);
            }
        
            let icframe_vercnt = (*negop).icframe_vercnt;
            let icmsg_vercnt = (*negop).icmsg_vercnt;
            let icversion_data = (*negop).icversion_data.as_mut_slice((icframe_vercnt + icmsg_vercnt) as usize);
            //let icversion_data = (*negop).icversion_data.as_mut_slice(((*negop).icframe_vercnt + (*negop).icmsg_vercnt) as usize);
            */

            ic_version_data[0].major = icframe_major as u16;
            ic_version_data[0].minor = icframe_minor as u16;
            ic_version_data[1].major = icmsg_major as u16;
            ic_version_data[1].minor = icmsg_major as u16;
       
            //TODO dump the negop data back into the buffer
            found_match
        }
}

fn vmbus_prep_negotiate_resp(icmsg_hdr: &mut bindings::icmsg_hdr,
                             buf: &mut [u8],
                             fw_versions: &[i32],
                             srv_versions: &[i32],
                             nego_fw_version: &mut i32,
                             nego_srv_version: &mut i32
                             ) -> bool {

        let buflen = buf.len();
        let mut fw_major;
        let mut fw_minor;
        let mut srv_major;
        let mut srv_minor;
        let mut found_match:bool = false;

        let mut negop: bindings::icmsg_negotiate = Default::default();
        
        pr_info!("t-megha Entering vmbus_prep_negotiate_resp");
        unsafe {
            /* Check that there's enough space for icframe_vercnt, icmsg_vercnt */
            if buflen < (super::ICMSG_HDR + offset_of!(bindings::icmsg_negotiate, reserved)).try_into().unwrap() {
                pr_err!("Invalid icmsg negotiate\n");
                return false;
            }

            icmsg_hdr.icmsgsize = 0x10;
            
            let mut start_offset = super::ICMSG_HDR;
            negop.icframe_vercnt = unsafe {
                let end_offset = start_offset + core::mem::size_of::<u16>();
                let ptr = buf[start_offset..end_offset].as_ptr() as *const u16;
                start_offset = end_offset;
                *ptr
            };
            let mut icframe_major = negop.icframe_vercnt;
            let mut icframe_minor = 0;

            negop.icmsg_vercnt = unsafe {
                let end_offset = start_offset + core::mem::size_of::<u16>();
                let ptr = buf[start_offset..end_offset].as_ptr() as *const u16;
                start_offset = end_offset;
                *ptr
            };
            let mut icmsg_major = negop.icmsg_vercnt;
            let mut icmsg_minor = 0;
        
            negop.reserved = unsafe {
                let end_offset = start_offset + core::mem::size_of::<u32>();
                let ptr = buf[start_offset..end_offset].as_ptr() as *const u32;
                start_offset = end_offset;
                *ptr
            };

            let total_ic_versions = negop.icframe_vercnt + negop.icmsg_vercnt;
            let mut ic_version_data: Vec<bindings::ic_version> = Vec::new();
            //let mut ic_version_data: Vec<bindings::ic_version> = vec![];
            let ptr = buf[start_offset..total_ic_versions as usize].as_ptr() as *const bindings::ic_version;
            unsafe {
                for i in 0..total_ic_versions {
                    ic_version_data.try_push(ptr.add(i.into()).read());
                }
            }

            for version in &ic_version_data{
                let ver_major = version.major;
                let ver_minor = version.minor;
                pr_info!("t-megha ic_version: major={}, minor={}", ver_major, ver_minor);
            }

            return false;
            //pr_info!("t-megha icframe_vercnt: {}, icmsg_vercnt: {}" , icframe_major, icmsg_major);
            pr_info!("t-megha printing from A icframe_major: {}, icframe_minor: {}, icmsg_major: {}, icmsg_minor: {}", icframe_major, icframe_minor, icmsg_major, icmsg_minor);
            
            //Validate a negop packet
        
            let negotiated_packet_size = icmsg_negotiate_pkt_size(icframe_major.into(), icmsg_major.into());
            if icframe_major as u32 > 
                bindings::IC_VERSION_NEGOTIATION_MAX_VER_COUNT || icmsg_major as u32 > 
                bindings::IC_VERSION_NEGOTIATION_MAX_VER_COUNT || negotiated_packet_size > buflen {
                    pr_err!("Invalid icmsg negotiate - icframe_major: {}, icmsg_major: {}\n", icframe_major, icmsg_major);
                    return resp_fw_srv_version(&mut negop, &mut ic_version_data,
                                           nego_fw_version,
                                           nego_srv_version,
                                           icframe_major,
                                           icframe_minor,
                                           icmsg_major,
                                           icmsg_minor,
                                           found_match);
            }
            
            /*
             * Select the framework version number we will support
             */
            
            //let icframe_vercnt = negop.icframe_vercnt;
            //let icmsg_vercnt = negop.icmsg_vercnt;
            //let icversion_data = negop.icversion_data.as_slice((icframe_vercnt + icmsg_vercnt) as usize);

            /*
            negop.icversion_data = unsafe {
                let end_offset = start_offset + (core::mem::size_of::<icmsg_negotiate>() - core::mem::size_of::<u16>() + core::mem::size_of::<u16>() + core::mem::size_of::<u32>());
                let ptr = buf[start_offset..end_offset].as_ptr() as *const usize;
                *ptr
            }
            let ic_version_data = negop.icversion_data.as_slice(negop.icframe_vercnt + negop.icmsg_vercnt);
            */
            
            //Select the framework version number
            
            for fw_version in fw_versions {
                fw_major = fw_version >> 16;
                fw_minor = fw_version & 0xFFFF;

                for j in 0..negop.icframe_vercnt as usize {
                    if i32::from(ic_version_data[j].major) == fw_major && i32::from(ic_version_data[j].minor) == fw_minor {
                        icframe_major = ic_version_data[j].major;
                        icframe_minor = ic_version_data[j].minor;
                        found_match = true;
                        break;
                    }
                }
                if found_match {
                    break;
                }
            }

        
            if !found_match {
                return resp_fw_srv_version(&mut negop, &mut ic_version_data, 
                                       nego_fw_version,
                                       nego_srv_version,
                                       icframe_major,
                                       icframe_minor,
                                       icmsg_major,
                                       icmsg_minor,
                                       found_match);
            }

            found_match = false;
            for srv_version in srv_versions {
                srv_major = srv_version >> 16;
                srv_minor = srv_version & 0xFFFF;
            
                for j in (negop.icframe_vercnt as usize)..(total_ic_versions as usize) {
                    if i32::from(ic_version_data[j].major) == srv_major && i32::from(ic_version_data[j].minor) == srv_minor {
                        icmsg_major = ic_version_data[j].major;
                        icmsg_minor = ic_version_data[j].minor;
                        found_match = true;
                        break;
                    }
                }
                if found_match {
                    break;
                }
            }
            pr_info!("t-megha Prep_negotiate working");
        
            resp_fw_srv_version(&mut negop, &mut ic_version_data,
                            nego_fw_version,
                            nego_srv_version,
                            icframe_major,
                            icframe_minor,
                            icmsg_major,
                            icmsg_minor,
                            found_match)
        }
}

pub fn prep_negotiate_resp(
    buf: &mut [u8],
    fw_versions: &[i32],
    srv_versions: &[i32],
) -> Option<(i32, i32)> {
    let mut fw = 0;
    let mut srv = 0;

    if buf.len() < super::BUSPIPE_HDR_SIZE {
        return None;
    }

    //Extract ICMSG HEADER from the buffer
    let mut icmsg_hdr: bindings::icmsg_hdr = unsafe {
        let start_offset = super::BUSPIPE_HDR_SIZE;
        let end_offset = super::ICMSG_HDR;
        let ptr = buf[start_offset..end_offset].as_ptr() as *const bindings::icmsg_hdr;
        *ptr
    };

    // SAFETY: All buffers are valid for the duration of this call due to their lifetimes.
    
    let res = unsafe {
        vmbus_prep_negotiate_resp(&mut icmsg_hdr, buf, fw_versions, srv_versions, &mut fw, &mut srv)
    };

    //let b = buf.as_mut_ptr();
    //let b_val = unsafe { b.offset(super::ICMSG_HDR.try_into().unwrap()) as *mut bindings::icmsg_negotiate };
    //pr_info!("t-megha Value of buf ptr -> {:#?}", b_val);
    pr_info!("t-megha Buf is -> {:?}", buf);
    
    /*
    let res = unsafe {
        bindings::vmbus_prep_negotiate_resp(
            buf[super::BUSPIPE_HDR_SIZE..super::BUSPIPE_HDR_SIZE + 20].as_mut_ptr().cast(),
            buf.as_mut_ptr(),
            buf.len().try_into().ok()?,
            fw_versions.as_ptr(),
            fw_versions.len().try_into().ok()?,
            srv_versions.as_ptr(),
            srv_versions.len().try_into().ok()?,
            &mut fw,
            &mut srv,
        )
    };
    */
    pr_info!(
        "t-megha This is the fw: {} and this is the srv: {} ",
        fw,
        srv
        );
    //pr_info!("t-megha Calling vmbus_prep_negotiate_resp {}", res);
    Some((fw, srv))
}

/// Declares a kernel module that exposes a single vmbus driver.
///
/// # Examples
///
/// ```ignore
/// # use kernel::prelude::*;
/// # use kernel::hv;
/// use kernel::hv::vmbus;
///
/// struct MyDriver;
/// impl vmbus::Driver for MyDriver {
///     // [...]
/// #    fn probe(_: &mut vmbus::Device, _: hv::ChannelToOpen, _: Option<&Self::IdInfo>) -> Result {
/// #        Ok(())
/// #    }
/// }
///
/// kernel::module_vmbus_driver! {
///     type: MyDriver,
///     name: "module_name",
///     author: "Author name <author@email.com>",
///     license: "GPL",
/// }
/// ```
#[macro_export]
macro_rules! module_vmbus_driver {
    ($($f:tt)*) => {
        $crate::module_driver!(<T>, $crate::hv::vmbus::Adapter<T>, { $($f)* });
    };
}

/// Defines the id table for vmbus devices.
///
/// # Examples
///
/// ```
/// # use kernel::prelude::*;
/// # use kernel::hv;
/// use kernel::hv::{guid, vmbus};
///
/// struct MyDriver;
/// impl vmbus::Driver for MyDriver {
///     // [...]
/// #    fn probe(_: &mut vmbus::Device, _: hv::ChannelToOpen, _: Option<&Self::IdInfo>) -> Result {
/// #        Ok(())
/// #    }
///     kernel::define_vmbus_id_table! {(), [
///         ({ guid: guid(b"13c2c235-9247-414c-9027-a96dc2b8b892") }, None ),
///     ]}
/// }
/// ```
#[macro_export]
macro_rules! define_vmbus_id_table {
    ($data_type:ty, $($t:tt)*) => {
        $crate::define_id_table!(ID_TABLE, $crate::hv::vmbus::DeviceId, $data_type, $($t)*);
    };
}

/// Defines a vmbus id table with a single id given by a guid.
///
/// There is no data associated with the id.
///
/// # Examples
///
/// ```ignore
/// # use kernel::prelude::*;
/// # use kernel::hv;
/// use kernel::hv::vmbus;
///
/// struct MyDriver;
/// impl vmbus::Driver for MyDriver {
///     // [...]
/// #    fn probe(_: &mut vmbus::Device, _: hv::ChannelToOpen, _: Option<&Self::IdInfo>) -> Result {
/// #        Ok(())
/// #    }
///     kernel::define_vmbus_single_id!("18cf0edb-1a1b-4f68-bca6-49f01899e264");
/// }
/// ```
#[macro_export]
macro_rules! define_vmbus_single_id {
    ($guid:literal) => {
        $crate::define_vmbus_id_table! {(), [
            ({guid: $crate::hv::guid(($guid).as_bytes())}, None),
        ]}
    };
}
