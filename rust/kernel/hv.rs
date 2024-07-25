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

/*
pub fn icmsg_negotiate_pkt_size(icframe_vercnt: usize, icmsg_vercnt: usize) -> usize {
    let sizeof_icmsg_negotiate = core::mem::size_of::<bindings::icmsg_negotiate>() as usize;
    let sizeof_ic_version = core::mem::size_of::<bindings::ic_version>() as usize;
    (ICMSG_HDR + sizeof_icmsg_negotiate) + (((icframe_vercnt) + (icmsg_vercnt)) * sizeof_ic_version)
}
*/

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

    fn error_clean_ring(newchannel: *mut bindings::vmbus_channel, err: core::ffi::c_int) -> i32 {
        unsafe {
            bindings::hv_ringbuffer_cleanup(&mut (*newchannel).outbound);
            bindings::hv_ringbuffer_cleanup(&mut (*newchannel).inbound);
            bindings::vmbus_free_requestor_for_binding_gen(&mut (*newchannel).requestor);
            err
        }
    }

    fn error_free_gpadl(newchannel: *mut bindings::vmbus_channel, err: core::ffi::c_int) -> i32 {
        unsafe {
            bindings::vmbus_teardown_gpadl(newchannel, &mut (*newchannel).ringbuffer_gpadlhandle);
            return Self::error_clean_ring(newchannel, err);
        }
    }

    fn error_free_info(
        newchannel: *mut bindings::vmbus_channel,
        open_info: *mut bindings::vmbus_channel_msginfo,
        err: core::ffi::c_int,
    ) -> i32 {
        unsafe {
            bindings::kfree(open_info as *const core::ffi::c_void);
            return Self::error_free_gpadl(newchannel, err);
        }
    }

    fn error_clean_msglist(
        flags: u64,
        entry: *mut bindings::list_head,
        open_info: *mut bindings::vmbus_channel_msginfo,
        newchannel: *mut bindings::vmbus_channel,
        err: core::ffi::c_int,
    ) -> i32 {
        unsafe {
            bindings::vmbus_spin_lock_unlock_irqsave_del(flags, entry);
            return Self::error_free_info(newchannel, open_info, err);
        }
    }

    fn __vmbus_open(
        newchannel: *mut bindings::vmbus_channel,
        userdata: &[u8],
        onchannelcallback: bindings::onchannel_t,
        context: *mut core::ffi::c_void,
    ) -> core::ffi::c_int {
        unsafe {
            #[allow(unused_assignments)]
            let mut open_info: *mut bindings::vmbus_channel_msginfo = core::ptr::null_mut();
            
            let open_msg: *mut bindings::vmbus_channel_open_channel;
            let page: *mut bindings::page = (*newchannel).ringbuffer_page;
            let send_pages: u32;
            let recv_pages: u32;
            let flags: u64 = 0;
            let mut err: core::ffi::c_int;
            let userdatalen = userdata.len();

            if userdatalen > bindings::MAX_USER_DEFINED_BYTES.try_into().unwrap() {
                return -(bindings::EINVAL as i32);
            }

            send_pages = (*newchannel).ringbuffer_send_offset;
            recv_pages = (*newchannel).ringbuffer_pagecount - send_pages;

            if (*newchannel).state != bindings::vmbus_channel_state_CHANNEL_OPEN_STATE {
                return -(bindings::EINVAL as i32);
            }

            if (*newchannel).rqstor_size != 0 {
                if bindings::vmbus_alloc_requestor_for_binding_gen(
                    &mut (*newchannel).requestor,
                    (*newchannel).rqstor_size,
                ) != 0
                {
                    return -(bindings::ENOMEM as i32);
                }
            }

            (*newchannel).state = bindings::vmbus_channel_state_CHANNEL_OPENING_STATE;
            (*newchannel).onchannel_callback = onchannelcallback;
            (*newchannel).channel_callback_context = context;

            if (*newchannel).max_pkt_size == 0 {
                (*newchannel).max_pkt_size = bindings::VMBUS_DEFAULT_MAX_PKT_SIZE;
            }

            (*newchannel).ringbuffer_gpadlhandle.gpadl_handle = 0;

            err = bindings::vmbus_establish_gpadl_for_binding_gen(
                newchannel,
                bindings::lowmem_page_address_for_binding_gen((*newchannel).ringbuffer_page),
                (send_pages + recv_pages) << bindings::PAGE_SHIFT,
                (*newchannel).ringbuffer_send_offset << bindings::PAGE_SHIFT,
                &mut (*newchannel).ringbuffer_gpadlhandle,
            );
            if err != 0 {
                return Self::error_clean_ring(newchannel, err);
            }

            err = bindings::hv_ringbuffer_init(&mut (*newchannel).outbound, page, send_pages, 0);

            if err != 0 {
                return Self::error_free_gpadl(newchannel, err);
            }

            err = bindings::hv_ringbuffer_init(
                &mut (*newchannel).inbound,
                page.offset(send_pages.try_into().unwrap()),
                recv_pages,
                (*newchannel).max_pkt_size,
            );

            if err != 0 {
                return Self::error_free_gpadl(newchannel, err);
            }

            let size = core::mem::size_of::<bindings::vmbus_channel_msginfo>()
                + core::mem::size_of::<bindings::vmbus_channel_open_channel>();
            open_info = bindings::__kmalloc(size, bindings::BINDINGS_GFP_KERNEL)
                as *mut bindings::vmbus_channel_msginfo;
            bindings::memset(
                open_info as *mut core::ffi::c_void,
                0,
                size.try_into().unwrap(),
            );

            if open_info.is_null() {
                err = -(bindings::ENOMEM as i32);
                return Self::error_free_gpadl(newchannel, err);
            }

            bindings::init_completion_for_binding_gen(&mut (*open_info).waitevent);

            (*open_info).waiting_channel = newchannel;

            let size = (*open_info).msgsize as usize;
            let open_msg_data = ((*open_info).msg).as_mut_slice(size);
            open_msg = open_msg_data.as_mut_ptr() as *mut bindings::vmbus_channel_open_channel;
            (*open_msg).header.msgtype =
                bindings::vmbus_channel_message_type_CHANNELMSG_OPENCHANNEL;
            (*open_msg).openid = (*newchannel).offermsg.child_relid;
            (*open_msg).child_relid = (*newchannel).offermsg.child_relid;
            (*open_msg).ringbuffer_gpadlhandle = (*newchannel).ringbuffer_gpadlhandle.gpadl_handle;
            (*open_msg).downstream_ringbuffer_pageoffset =
                bindings::hv_ring_gpadl_send_hvpgoffset_for_binding_gen(
                    send_pages << bindings::PAGE_SHIFT,
                );
            let target_vp: i32 = bindings::hv_cpu_number_to_vp_number_for_binding_gen(
                (*newchannel).target_cpu.try_into().unwrap(),
            );
            (*open_msg).target_vp = target_vp as u32;

            if userdatalen != 0 {
                (*open_msg).userdata[..userdatalen].copy_from_slice(&userdata[..userdatalen]);
            }

            bindings::vmbus_spin_lock_unlock_irqsave_add_tail(
                flags,
                &mut (*open_info).msglistentry,
            );

            if (*newchannel).rescind {
                err = -(bindings::ENODEV as i32);
                return Self::error_clean_msglist(
                    flags,
                    &mut (*open_info).msglistentry,
                    open_info,
                    newchannel,
                    err,
                );
            }

            err = bindings::vmbus_post_msg(
                open_msg as *mut core::ffi::c_void,
                core::mem::size_of::<bindings::vmbus_channel_open_channel>(),
                true,
            );

            if err != 0 {
                Self::error_clean_msglist(
                    flags,
                    &mut (*open_info).msglistentry,
                    open_info,
                    newchannel,
                    err,
                );
            }

            bindings::wait_for_completion(&mut (*open_info).waitevent);
            bindings::vmbus_spin_lock_unlock_irqsave_del(flags, &mut (*open_info).msglistentry);

            if (*newchannel).rescind {
                err = -(bindings::ENODEV as i32);
                return Self::error_free_info(newchannel, open_info, err);
            }

            let status = (*open_info).response.open_result.status;
            if status != 0 {
                err = -(bindings::EAGAIN as i32);
                return Self::error_free_info(newchannel, open_info, err);
            }

            (*newchannel).state = bindings::vmbus_channel_state_CHANNEL_OPENED_STATE;

            bindings::kfree(open_info as *const core::ffi::c_void);

            err
        }
    }

    fn vmbus_open(
        newchannel: *mut bindings::vmbus_channel,
        send_ringbuffer_size: usize,
        recv_ringbuffer_size: usize,
        userdata: &[u8],
        onchannelcallback: bindings::onchannel_t,
        context: *mut core::ffi::c_void,
    ) -> core::ffi::c_int {
        #[allow(unused_assignments)]
        let mut err: i32 = 0;

        err = unsafe {
            bindings::vmbus_alloc_ring(
                newchannel,
                send_ringbuffer_size.try_into().unwrap(),
                recv_ringbuffer_size.try_into().unwrap(),
            )
        };
        if err != 0 {
            return err;
        }

        err = Self::__vmbus_open(newchannel, userdata, onchannelcallback, context);

        if err != 0 {
            unsafe { bindings::vmbus_free_ring(newchannel) };
        }

        pr_info!("Rust: A channel is opened");

        err
    }

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

        to_result(Self::vmbus_open(
            ptr,
            send_ringbuffer_size,
            recv_ringbuffer_size,
            userdata,
            Some(Self::callback::<H>),
            context_ptr as _,
        ))?;

        // SAFETY: By the type invariants, we know that `self.0` is valid and that the channel is
        // not opened yet. The userdata pointers are also valid for the duration of this call,
        // given that the lifetime on the shared borrow guarantees it.
        
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
    
    /// Handles disconnecting the ring and 
    /// dropping the mappings of ring buffers
    pub fn vmbus_close(channel: *mut bindings::vmbus_channel) {
        let disconnect_ring: core::ffi::c_int = unsafe { bindings::vmbus_disconnect_ring(channel) };
        if disconnect_ring == 0 {
            unsafe {
                bindings::vmbus_free_ring(channel);
            }
        }
        pr_info!("Rust: Closing a channel");
    }

    /// Manually closes the channel and returns a new channel and the data.
    ///
    /// The returned values can be reused later to re-open the channel.
    pub fn close(self) -> (ChannelToOpen, T) {
        // SAFETY: The type invariants guarantee that the channel is valid and opened.
        Self::vmbus_close(self.ptr);
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

impl Channel {

    /// Reads from the ring buffer
    pub fn hv_ringbuffer_read(
        channel: *mut bindings::vmbus_channel,
        buffer: *mut core::ffi::c_void,
        buflen: u32,
        buffer_actual_len: *mut u32,
        requestid: *mut u64,
        raw: bool,
    ) -> core::ffi::c_int {
        let desc: *mut bindings::vmpacket_descriptor;
        let packetlen: u32;
        let offset: u32;

        if buflen == 0 {
            return -(bindings::EINVAL as i32);
        }

        //SAFETY: call to an unsafe function
        unsafe {
            desc = bindings::hv_pkt_iter_first(channel);
        }

        if desc.is_null() {
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
            return -(bindings::ENOBUFS as i32);
        }

        unsafe {
            bindings::memcpy(
                buffer,
                ((desc as *const u8).add(offset as usize)) as *const core::ffi::c_void,
                packetlen.into(),
            );

            bindings::__hv_pkt_iter_next(channel, desc);

            bindings::hv_pkt_iter_close(channel);
        }

        0
    }

    /// Retrieves the user packet on the specified channel
    /// directly from the Hyper-V vmbus and puts the data
    /// it received into Buffer.
    ///
    /// Recieves the data unparsed from Hyper-V
    pub fn __vmbus_recvpacket(
        channel: *mut bindings::vmbus_channel,
        buffer: *mut core::ffi::c_void,
        bufferlen: u32,
        buffer_actual_len: *mut u32,
        requestid: *mut u64,
        raw: bool,
    ) -> core::ffi::c_int {
        Self::hv_ringbuffer_read(
            channel,
            buffer,
            bufferlen,
            buffer_actual_len,
            requestid,
            raw,
        )
    }

    /// Handles high-level packets that are recieved
    pub fn vmbus_recvpacket(
        channel: *mut bindings::vmbus_channel,
        buffer: *mut core::ffi::c_void,
        bufferlen: u32,
        buffer_actual_len: *mut u32,
        requestid: *mut u64,
    ) -> core::ffi::c_int {
        Self::__vmbus_recvpacket(
            channel,
            buffer,
            bufferlen,
            buffer_actual_len,
            requestid,
            false,
        )
    }

    /// Receives a packet from the channel.
    ///
    /// On success, returns the request id and the actual received size on success.
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
        ))?;

        Ok((request_id, read_len as _))
    }

    fn align(x: u32, mask: u32) -> u32 {
        (x + mask) & !mask
    }

    /// Sends the specified buffer on the given channel
    /// 
    /// `channel` is a pointer to a vmbus_channel structure
    /// `buffer` is a pointer to the buffer you want to send the data from                                /// `bufferlen` is the maximum size of what the buffer holds
    /// `requestid` is an identifier of the request
    /// `trans_id is the identifier of the transaction assosciated to this request
    /// `type` of packet that is being sent
    ///
    /// Directly sends unparsed data to Hyper-V
    pub fn vmbus_sendpacket_getid(
        channel: *mut bindings::vmbus_channel,
        buffer: *mut core::ffi::c_void,
        bufferlen: u32,
        requestid: u64,
        trans_id: *mut u64,
        type_: bindings::vmbus_packet_type,
        flags: u32,
    ) -> core::ffi::c_int {
        let packetlen: u32 =
            core::mem::size_of::<bindings::vmpacket_descriptor>() as u32 + bufferlen;
        let packetlen_aligned: u32 = Self::align(packetlen, core::mem::size_of::<u64>() as u32);
        
        /* Setup the descriptor */
        let mut desc = bindings::vmpacket_descriptor {
            type_: type_.try_into().unwrap(),
            flags: flags.try_into().unwrap(),
            offset8: (core::mem::size_of::<bindings::vmpacket_descriptor>() >> 3) as u16,
            len8: (packetlen_aligned >> 3) as u16,
            trans_id: core::u64::MAX - 1,
        };

        let aligned_data: u64 = 0;
        let bufferlist: &[bindings::kvec; 3] = &[
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
            },
        ];
        let bufferlist_ptr: *const bindings::kvec = bufferlist.as_ptr();
        let num_vecs: u32 = if bufferlen != 0 { 3 } else { 1 };

        unsafe {
            bindings::hv_ringbuffer_write(channel, bufferlist_ptr, num_vecs, requestid, trans_id)
        }
    }

    /// Sends the specified buffer on the given channel
    ///
    /// `channel` is a pointer to a vmbus_channel structure
    /// `buffer` is a pointer to the buffer you want to send the data from
    /// `bufferlen` is the maximum size of what the buffer holds
    /// `requestid` is an identifier of the request
    /// `type` is the type of packet that is being sent eg: negotiate, time packet etc.
    ///
    /// Sends data in @buffer directly to Hyper-V via the vmbus
    /// This will send the data unparsed to Hyper-V
    pub fn vmbus_sendpacket(
        channel: *mut bindings::vmbus_channel,
        buffer: *mut core::ffi::c_void,
        bufferlen: u32,
        requestid: u64,
        type_: bindings::vmbus_packet_type,
        flags: u32,
    ) -> core::ffi::c_int {
        Self::vmbus_sendpacket_getid(
            channel,
            buffer,
            bufferlen,
            requestid,
            core::ptr::null_mut(),
            type_,
            flags,
        )
    }

    /// Sends a packet on the channel.
    pub fn send_packet(&self, buf: &[u8], requestid: u64, packet_type: PacketType) -> Result {
        // SAFETY: The channel is opened by the type invariants. All other pointers are valid for
        // the duration of this call.
        to_result(Self::vmbus_sendpacket(
            self.0.get(),
            buf.as_ptr() as *mut _,
            buf.len().try_into()?,
            requestid,
            packet_type as _,
            0,
        ))
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
