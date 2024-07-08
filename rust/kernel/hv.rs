// SPDX-License-Identifier: GPL-2.0

//! Hyper-V interfaces.
//!
//! C header: [`include/linux/hyperv.h`](../../../../include/linux/hyperv.h)

use crate::{
    bindings, error::to_result, error::Result, types::ForeignOwnable, types::Opaque,
    types::ScopeGuard,
};

use kernel::prelude::*;

pub use bindings::{heartbeat_msg_data, icmsg_hdr};
use core::marker::PhantomData;

#[cfg(CONFIG_HYPERV_UTILS)]
pub mod util;
pub mod vmbus;

/// The page size with which Hyper-V runs.
pub const HYP_PAGE_SIZE: usize = 1 << bindings::HV_HYP_PAGE_SHIFT;

/// Size of the C `vmbuspipe_hdr` type.
pub const BUSPIPE_HDR_SIZE: usize = core::mem::size_of::<bindings::vmbuspipe_hdr>();

/// Size of the C `vmbuspipe_hdr` and `icmsg_hdr` types, which are the beginning of packets
/// received through a [`Channel`].
pub const ICMSG_HDR: usize = BUSPIPE_HDR_SIZE + core::mem::size_of::<bindings::icmsg_hdr>();

pub fn icmsg_negotiate_pkt_size(icframe_vercnt: usize, icmsg_vercnt: usize) -> usize {
    let sizeof_icmsg_negotiate = core::mem::size_of::<bindings::icmsg_negotiate>() as usize;
    let sizeof_ic_version = core::mem::size_of::<bindings::ic_version>() as usize;
    (ICMSG_HDR + sizeof_icmsg_negotiate) + (((icframe_vercnt) + (icmsg_vercnt)) * sizeof_ic_version)
}

/// Specifies the type of a packet to be sent via [`Channel::send_packet`] and variants.
#[repr(u32)]
pub enum PacketType {
    /// Data is included in the packet.
    DataInband = bindings::vmbus_packet_type_VM_PKT_DATA_INBAND,
}

/// Channel callback modes.
///
/// These are used in [`ChannelToOpenl:set_read_mode`].
#[repr(u32)]
pub enum CallMode {
    /// Callback called from taslket and should read channel until empty. Interrupts from the host
    /// are masked while read is in process (default).
    Batched = bindings::vmbus_channel_hv_callback_mode_HV_CALL_BATCHED,

    /// Callback called from tasklet (softirq).
    Direct = bindings::vmbus_channel_hv_callback_mode_HV_CALL_DIRECT,
    // TODO: Bring this back eventually.
    //
    // N.B. When we do bring this back, the context data associated with the channel callback will
    // need to be shared as ISRs can be called concurrently from multiple CPUs.
    //    /// Callback called in interrupt context and must invoke its own deferred processing. Host
    //    /// interrupts are disabled and must be re-enabled when ring is empty.
    //    Isr = bindings::vmbus_channel_hv_callback_mode_HV_CALL_ISR,
}

/// A channel on a vmbus bus that is ready to be opened.
///
/// Wraps the kernel's C `struct vmbus_channel` when it's in `CHANNEL_OPEN_STATE` state.
///
/// # Invariants
///
/// `0` points to a valid channel that is ready to be opened. Additionally, this instance of
/// [`ChannelToOpen`] holds a refcount increment in `0`.
pub struct ChannelToOpen(*mut bindings::vmbus_channel);

// SAFETY: This just wraps a vmbus channel, which can be used from any thread/cpu.
unsafe impl Send for ChannelToOpen {}

// SAFETY: This just wraps a vmbus channel, which can be used from any thread/cpu.
unsafe impl Sync for ChannelToOpen {}

impl ChannelToOpen {
    /// Creates a new instance of a `ChannelToOpen`.
    ///
    /// # Safety
    ///
    /// `ptr` must point to a valid new channel.
    unsafe fn new(ptr: *mut bindings::vmbus_channel) -> Self {
        // INVARIANT: Incrementing the refcount on `ptr`, so this instances owns the increment.
        //
        // SAFETY: The safety requirements ensure that `ptr` is valid, so we can increment the
        // refocunt.
        unsafe { bindings::kobject_get(&mut (*ptr).kobj) };
        Self(ptr)
    }

    /// Sets the channel's read mode.
    pub fn set_read_mode(&mut self, mode: CallMode) {
        // SAFETY: `self.0` is valid and the channel is not opened yet, so it is safe to change the
        // read mode.
        unsafe { bindings::set_channel_read_mode(self.0, mode as _) };
    }

    /*
    fn vmbus_open(newchannel: &mut bindings::vmbus_channel,
                  send_ringbuffer_size: u32,
                  recv_ringbuffer_size: u32,
                  userdata: &mut core::ffi::c_void,
                  userdatalen: u32,
                  onchannelcallback: bindings::onchannel_t,
                  context: &mut core::ffi::c_void
                  ) -> i32 {
        let mut err: i32 = 0;

        err = bindings::vmbus_alloc_ring(newchannel,
                                         send_ringbuffer_size,
                                         recv_ringbuffer_size,
                                         );
        if err != 0 {
            return err;
        }
        
        err = Self::__vmbus_open(newchannel,
                                     userdata,
                                     userdatalen,
                                     onchannelcallback,
                                     context);

        if err != 0 {
            bindings::vmbus_free_ring(newchannel);
        }
        
        err
    }
    */

    /// Opens the channel.
    pub fn open<H: ChannelDataHandler>(
        self,
        send_ringbuffer_size: usize,
        recv_ringbuffer_size: usize,
        userdata: &[u8],
        context: H::Context,
    ) -> Result<ChannelCloser<H::Context>> {
        let context_ptr = context.into_foreign();
        let guard = ScopeGuard::new(|| {
            // SAFETY: `contex_ptr` just came from a call to `into_pointer` and if the guard runs,
            // there won't be any users of it anymore.
            unsafe { H::Context::from_foreign(context_ptr) };
        });
        let ptr = self.0;
        pr_info!("t-megha Calling vmbus_open, {} ", send_ringbuffer_size);
        // SAFETY: By the type invariants, we know that `self.0` is valid and that the channel is
        // not opened yet. The userdata pointers are also valid for the duration of this call,
        // given that the lifetime on the shared borrow guarantees it.
        to_result(unsafe {
            bindings::vmbus_open(
                ptr,
                send_ringbuffer_size.try_into()?,
                recv_ringbuffer_size.try_into()?,
                userdata.as_ptr() as _,
                userdata.len().try_into()?,
                Some(Self::callback::<H>),
                context_ptr as _,
            )
        })?;
        //pr_info!("t-megha Calling vmbus_open");
        core::mem::forget(self);
        guard.dismiss();
        // INVARIANT: We are transferring the ownership of the refcount increment to the
        // `ChannelCloser` instance.
        Ok(ChannelCloser {
            ptr,
            context: context_ptr,
            _p: PhantomData,
        })
    }

    unsafe extern "C" fn callback<H: ChannelDataHandler>(
        chan: *mut bindings::vmbus_channel,
        context: *mut core::ffi::c_void,
    ) {
        // SAFETY: Given that the channel can only be in batched and direct call modes, the
        // callback is guaranteed to not run concurrently, so it's safe to borrow the context data
        // mutably.
        let data = unsafe { H::Context::borrow_mut(context) };

        // SAFETY: The channel is valid by the C contract, so it's safe to cast it to the
        // transparent `Channel` type.
        let channel = unsafe { &*(chan as *const Channel) };
        H::handle_data(data, channel)
    }
}

impl Drop for ChannelToOpen {
    fn drop(&mut self) {
        // SAFETY: The type invariants guarantee that this object holds a reference to the channel.
        unsafe { bindings::kobject_put(&mut (*self.0).kobj) };
    }
}

/// Closes the channel and frees any associated resources when it goes out of scope.
///
/// # Invariants
///
/// `ptr` points to a valid channel that is opened. Additionally, this instance of [`ChannelCloser`]
/// holds a refcount increment in `ptr`.
pub struct ChannelCloser<T: ForeignOwnable> {
    ptr: *mut bindings::vmbus_channel,
    context: *const core::ffi::c_void,
    _p: PhantomData<T>,
}

// SAFETY: This wraps a vmbus channel, which can be used from any thread/cpu. It also holds context
// data, so it is `Send` as long as the context data also is.
unsafe impl<T: ForeignOwnable + Send> Send for ChannelCloser<T> {}

// SAFETY: This wraps a vmbus channel, which can be used from any thread/cpu. It also holds context
// data, so it is `Sync` as long as the context data also is.
unsafe impl<T: ForeignOwnable + Sync> Sync for ChannelCloser<T> {}

impl<T: ForeignOwnable> ChannelCloser<T> {
    /// Manually closes the channel and returns a new channel and the data.
    ///
    /// The returned values can be reused later to re-open the channel.
    
    /* COMPLETE THIS
    pub fn vmbus_free_ring(channel: *mut bindings::vmbus_channel) {
        bindings::hv_ringbuffer_cleanup(&channel.outbound);
        bindings::hv_ringbuffer_cleanup(&channel.inbound);

        if channel.ringbuffer_page) {
            bindings::__free_pages(channel.ringbuffer_page, getorder(channel.ringbuffer_pagecount << bindings::PAGE_SHIFT));
            channel.ringbuffer_page = 
*/
    pub fn vmbus_close(channel: *mut bindings::vmbus_channel) {
        let disconnect_ring: core::ffi::c_int = unsafe { bindings::vmbus_disconnect_ring(channel) };
        if disconnect_ring == 0 {
            unsafe { 
                bindings::vmbus_free_ring(channel); 
            }
        }
    }

    pub fn close(self) -> (ChannelToOpen, T) {
        // SAFETY: The type invariants guarantee that the channel is valid and opened.
        unsafe { Self::vmbus_close(self.ptr) };
        pr_info!("t-megha Calling vmbus_close");
        // SAFETY: `self.context` came from a previous call to `into_foreign`. Having closed the
        // channel above, we know there are no more references to it.
        let data = unsafe { T::from_foreign(self.context) };

        // INVARIANT: The increment of the refcount is transferred to the `ChannelToOpen` instance.
        let new_chan = ChannelToOpen(self.ptr);
        core::mem::forget(self);
        (new_chan, data)
    }
}

impl<T: ForeignOwnable> Drop for ChannelCloser<T> {
    fn drop(&mut self) {
        // SAFETY: The type invariants guarantee that the channel is valid and opened.
        unsafe { bindings::vmbus_close(self.ptr) };

        // SAFETY: The type invariants guarantee that this object holds a reference to the channel.
        unsafe { bindings::kobject_put(&mut (*self.ptr).kobj) };

        // SAFETY: `self.context` came from a previous call to `into_foreign`. Having closed the
        // channel above, we know there are no more references to it.
        unsafe { T::from_foreign(self.context) };
    }
}

/// A handler of data on a channel.
pub trait ChannelDataHandler {
    /// The context data associated with and made available to the handler.
    type Context: ForeignOwnable + Sync + Send;

    /// Called from interrupt context when the irq happens.
    fn handle_data(data: <Self::Context as ForeignOwnable>::BorrowedMut<'_>, chan: &Channel);
}

/// An open channel on a vmbus bus.
///
/// Wraps the kernel's C `struct vmbus_channel` when it's in `CHANNEL_OPENED_STATE` state.
///
/// # Invariants
///
/// The channel is opened.
#[repr(transparent)]
pub struct Channel(Opaque<bindings::vmbus_channel>);

/*
pub struct Kvec {
    iov_base: *mut core::ffi::c_void,
    iov_len: usize,
}
*/

impl Channel {
    /// Receives a packet from the channel.
    ///
    /// On success, returns the request id and the actual received size on success.
    
     pub fn hv_ringbuffer_read(channel: *mut bindings::vmbus_channel,
                              buffer: *mut core::ffi::c_void,
                              buflen: u32,
                              buffer_actual_len: *mut u32,
                              requestid: *mut u64,
                              raw: bool
                              ) -> core::ffi::c_int {
        let desc: *mut bindings::vmpacket_descriptor;
        let packetlen: u32;
        let offset: u32;

        if buflen == 0 { //   CHANGE/ADD DEFINITION FOR UNLIKELY()
            //return Err(-EINVAL); //EINVAL
            //let einval: i32 = -(bindings::EINVAL);
            //return einval;
            return -22;
        }

        //SAFETY: call to an unsafe function
        unsafe {
            desc = bindings::hv_pkt_iter_first(channel);
        }
        
        if desc.is_null() {
            //pr_info!("t-megha ringbuffer read working");
            return 0;
        }
        
        //SAFETY: dereference of a raw pointer in unsafe
        unsafe {
            offset = if raw != false { 
                0 
            } else {
                ((*desc).offset8 << 3).into()
            };
            packetlen = ((*desc).len8 << 3) as u32 - offset;
            *buffer_actual_len = packetlen;
            *requestid = (*desc).trans_id;
        }

        if packetlen > buflen {
            //return ENOBUFS;
            return -55;
        }
        //pr_info!("t-megha Calling Ringbuffer Read");

        unsafe {
            bindings::memcpy(buffer, ((desc as *const u8).add(offset as usize)) as *const core::ffi::c_void, packetlen.into()); 

            bindings::__hv_pkt_iter_next(channel, desc);

            bindings::hv_pkt_iter_close(channel);
        }

        0
    }
    

    pub fn __vmbus_recvpacket(channel: *mut bindings::vmbus_channel,
                              buffer: *mut core::ffi::c_void,
                              bufferlen: u32,
                              buffer_actual_len: *mut u32,
                              requestid: *mut u64,
                              raw: bool
                              ) -> core::ffi::c_int {
        Self::hv_ringbuffer_read(channel, buffer, bufferlen, buffer_actual_len, requestid, raw)
    }

    pub fn vmbus_recvpacket(channel: *mut bindings::vmbus_channel,
                            buffer: *mut core::ffi::c_void,
                            bufferlen: u32,
                            buffer_actual_len: *mut u32,
                            requestid: *mut u64
                            ) -> core::ffi::c_int {
        //pr_info!("t-megha recieve called from here");
        Self::__vmbus_recvpacket(channel, buffer, bufferlen, buffer_actual_len, requestid, false)
    }

    pub fn recv_packet(&self, buf: &mut [u8]) -> Result<(u64, usize)> {
        let mut read_len = 0;
        let mut request_id = 0;

        // SAFETY: The channel is opened by the type invariants. All other pointers are valid for
        // the duration of this call.
        to_result(Self::vmbus_recvpacket(
                self.0.get(),
                buf.as_mut_ptr().cast(),
                buf.len().try_into()?,
                &mut read_len,
                &mut request_id,
            )
        )?;

        Ok((request_id, read_len as _))
    }

    fn align(x: u32, mask: u32) -> u32 {
        (x + mask) & !mask
    }

    pub fn vmbus_sendpacket_getid(channel: *mut bindings::vmbus_channel,
                                  buffer: *mut core::ffi::c_void,
                                  bufferlen: u32,
                                  requestid: u64,
                                  trans_id: *mut u64,
                                  type_: bindings::vmbus_packet_type,
                                  flags: u32
                                  ) -> core::ffi::c_int {
        let packetlen:u32 = core::mem::size_of::<bindings::vmpacket_descriptor>() as u32 + bufferlen;
        let packetlen_aligned:u32 = Self::align(packetlen, core::mem::size_of::<u64>() as u32);
        let mut desc = bindings::vmpacket_descriptor {
            type_: type_.try_into().unwrap(),
            flags: flags.try_into().unwrap(),
            offset8: (core::mem::size_of::<bindings::vmpacket_descriptor>() >> 3) as u16,
            len8: (packetlen_aligned >> 3) as u16,
            trans_id: core::u64::MAX - 1,
        };
        let aligned_data: u64 = 0;
        //pr_info!("t-megha sendpacket_getid called from Rust");
        let bufferlist:&[bindings::kvec; 3] = &[
            bindings::kvec {
                iov_base: &mut desc as *mut bindings::vmpacket_descriptor as *mut core::ffi::c_void,
                iov_len: core::mem::size_of::<bindings::vmpacket_descriptor>(),
            },
            bindings::kvec {
                iov_base: buffer,
                iov_len: bufferlen as usize,
            },
            bindings::kvec {
                iov_base: &aligned_data as *const u64 as *mut core::ffi::c_void,
                iov_len: (packetlen_aligned - packetlen) as usize,
            }
        ];
        let bufferlist_ptr: *const bindings::kvec = bufferlist.as_ptr();
        let num_vecs: u32 = if bufferlen != 0 { 3 } else { 1 };

        unsafe{
            bindings::hv_ringbuffer_write(channel, bufferlist_ptr, num_vecs, requestid, trans_id)
        }
    }

    pub fn vmbus_sendpacket(channel: *mut bindings::vmbus_channel,
                        buffer: *mut core::ffi::c_void,
                        bufferlen: u32,
                        requestid: u64,
                        type_: bindings::vmbus_packet_type,
                        flags: u32) -> core::ffi::c_int {
        //pr_info!("t-megha SENDPACKET called successfully from here.");
        Self::vmbus_sendpacket_getid(channel, buffer, bufferlen, requestid, core::ptr::null_mut(), type_, flags) 
    }

    /// Sends a packet on the channel.
    pub fn send_packet(&self, buf: &[u8], requestid: u64, packet_type: PacketType) -> Result {
        // SAFETY: The channel is opened by the type invariants. All other pointers are valid for
        // the duration of this call.
        // pr_info!("t-megha SENDPACKET called successfully.");
        to_result(
            Self::vmbus_sendpacket(
                self.0.get(),
                buf.as_ptr() as *mut _,
                buf.len().try_into()?,
                requestid,
                packet_type as _,
                0,
            )
        )
    }
}

/// Parses a string into a GUID.
///
/// This function is const, so it can convert string at compile time.
pub const fn guid(input: &[u8]) -> [u8; 16] {
    const fn hex(c: u8) -> u8 {
        c - if c >= b'0' && c <= b'9' {
            b'0'
        } else if c >= b'a' && c <= b'f' {
            b'a' - 10
        } else if c >= b'A' && c <= b'F' {
            b'A' - 10
        } else {
            panic!("Invalid guid");
        }
    }
    const INDICES: &[usize] = &[6, 4, 2, 0, 11, 9, 16, 14, 19, 21, 24, 26, 28, 30, 32, 34];
    let mut result = [0; 16];

    let mut i = 0;
    while i < INDICES.len() {
        result[i] = hex(input[INDICES[i]]) << 4 | hex(input[INDICES[i] + 1]);
        i += 1;
    }

    result
}

