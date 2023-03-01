// Copyright 2023 Linaro Ltd. All Rights Reserved.
//          Viresh Kumar <viresh.kumar@linaro.org>
//
// Xen specific memory mapping implementations
//
// SPDX-License-Identifier: Apache-2.0 or BSD-3-Clause

//! Helper structure for working with mmaped memory regions on Xen.

use bitflags::bitflags;
use libc::{c_int, c_void, off_t, MAP_SHARED, PROT_READ, PROT_WRITE, _SC_PAGESIZE};
use std::{
    alloc::{self, handle_alloc_error, Layout},
    io,
    mem::{align_of, size_of},
    os::raw::c_ulong,
    os::unix::io::AsRawFd,
    ptr::null_mut,
    slice,
    sync::{Arc, Mutex},
};

use vmm_sys_util::ioctl::{ioctl_expr, ioctl_with_ref, _IOC_NONE};

use crate::guest_memory::{FileOffset, GuestAddress};
use crate::mmap::{MappedAddress, MappedAddressSimple, MmapInternal};
use crate::mmap_unix::{self, Error, Result};

fn page_size() -> u64 {
    // SAFETY: Safe because this call just returns the page size and doesn't have any side effects.
    unsafe { libc::sysconf(_SC_PAGESIZE) as u64 }
}

fn pages(size: usize) -> (usize, usize) {
    let page_size = page_size() as usize;
    let num = (size + page_size - 1) / page_size;

    (num, page_size * num)
}

// Bit mask for the vhost-user xen mmap message.
bitflags! {
    /// Flags for the Xen mmap message.
    pub struct MmapXenFlags: u32 {
        /// Xen foreign memory (accessed via /dev/privcmd).
        const FOREIGN = 0x1;
        /// Xen grant memory (accessed via /dev/gntdev).
        const GRANT = 0x2;
        /// Xen no advance mapping.
        const NO_ADVANCE_MAP = 0x8;
        /// All valid mappings.
        const ALL = Self::FOREIGN.bits() | Self::GRANT.bits();
    }
}

impl MmapXenFlags {
    /// Mmap flags are valid.
    pub fn is_valid(flags: u32) -> bool {
        // Only of one of FOREIGN or GRANT should be set and mmap_in_advance() should be true with
        // FOREIGN.
        if Self::is_foreign(flags) {
            if Self::is_grant(flags) || !Self::mmap_in_advance(flags) {
                return false;
            }
        } else if !Self::is_grant(flags) {
            return false;
        }

        true
    }

    /// Is xen foreign memory.
    pub fn is_foreign(flags: u32) -> bool {
        flags & Self::FOREIGN.bits() != 0
    }

    /// Is xen grant memory.
    pub fn is_grant(flags: u32) -> bool {
        flags & Self::GRANT.bits() != 0
    }

    /// Can mmap entire region in advance.
    pub fn mmap_in_advance(flags: u32) -> bool {
        flags & Self::NO_ADVANCE_MAP.bits() == 0
    }
}

/// Xen Foreign memory mapping interface.

#[repr(C)]
#[derive(Debug, Copy, Clone)]
/// Privcmd mmap batch v2 command
///
/// include/uapi/xen/privcmd.h: `privcmd_mmapbatch_v2`
struct PrivCmdMmapBatchV2 {
    /// number of pages to populate
    num: u32,
    /// target domain
    domid: u16,
    /// virtual address
    addr: *mut c_void,
    /// array of mfns
    arr: *const u64,
    /// array of error codes
    err: *mut c_int,
}

const XEN_PRIVCMD_TYPE: u32 = 'P' as u32;

// #define IOCTL_PRIVCMD_MMAPBATCH_V2 _IOC(_IOC_NONE, 'P', 4, sizeof(privcmd_mmapbatch_v2_t))
fn ioctl_privcmd_mmapbatch_v2() -> c_ulong {
    ioctl_expr(
        _IOC_NONE,
        XEN_PRIVCMD_TYPE,
        4,
        size_of::<PrivCmdMmapBatchV2>() as u32,
    )
}

#[derive(Copy, Clone, Debug, PartialEq)]
/// Xen foreign memory specific mmap() implementation.
pub struct MmapXenForeign {
    domid: u32,
    guest_base: GuestAddress,
    xen_flags: u32,
    addr: Option<*mut u8>,
    size: usize,
    fd: i32,
}

impl MmapXenForeign {
    /// Create a new object.
    pub fn new_with(domid: u32, guest_base: GuestAddress, xen_flags: u32) -> Result<Self> {
        let map = Self {
            domid,
            guest_base,
            xen_flags: xen_flags | MmapXenFlags::FOREIGN.bits(),
            addr: None,
            size: 0,
            fd: 0,
        };

        if MmapXenFlags::is_valid(map.xen_flags) {
            Ok(map)
        } else {
            Err(Error::XenMmapFlags(map.xen_flags))
        }
    }

    fn mmap_ioctl(&self, count: usize, addr: *mut u8) -> Result<()> {
        let base = self.guest_base.0 / page_size();

        let mut pfn = Vec::with_capacity(count);
        for i in 0..count {
            pfn.push(base + i as u64);
        }

        let mut err: Vec<c_int> = vec![0; count];

        let map = PrivCmdMmapBatchV2 {
            num: count as u32,
            domid: self.domid as u16,
            addr: addr as *mut c_void,
            arr: pfn.as_ptr(),
            err: err.as_mut_ptr(),
        };

        // SAFETY: This is safe because the ioctl guarantees to not access memory beyond
        // privcmd_ptr.
        let ret = unsafe { ioctl_with_ref(self, ioctl_privcmd_mmapbatch_v2(), &map) };

        if ret == 0 {
            Ok(())
        } else {
            Err(Error::Mmap(io::Error::last_os_error()))
        }
    }
}

impl AsRawFd for MmapXenForeign {
    fn as_raw_fd(&self) -> i32 {
        self.fd
    }
}

impl MmapInternal for MmapXenForeign {
    /// Mapped address for the region.
    fn addr(&self) -> *mut u8 {
        self.addr.unwrap()
    }

    /// Set mapped address for the region.
    fn set_addr(&mut self, addr: *mut u8) -> Result<()> {
        self.addr = Some(addr);
        Ok(())
    }

    /// Maps the memory in architecture / platform dependent way.
    fn mmap(
        &mut self,
        size: usize,
        prot: i32,
        flags: i32,
        file_offset: &Option<FileOffset>,
    ) -> Result<()> {
        let (fd, f_off) = if let Some(ref f_off) = file_offset {
            (f_off.file().as_raw_fd(), f_off.start())
        } else {
            (-1, 0)
        };

        let (count, size) = pages(size);
        let addr = mmap_unix::mmap(size, prot, flags | MAP_SHARED, fd, f_off as off_t)?;
        self.fd = fd;
        self.mmap_ioctl(count, addr)?;

        self.addr = Some(addr);
        self.size = size;

        Ok(())
    }

    /// Unmaps the memory in architecture / platform dependent way.
    fn munmap(&self) {
        // SAFETY: This is safe because we mapped the addr earlier.
        unsafe {
            libc::munmap(self.addr() as *mut c_void, self.size);
        }
    }

    /// Mmap specific flags.
    fn mmap_flags(&self) -> u32 {
        self.xen_flags
    }

    /// Mmap specific data.
    fn mmap_data(&self) -> u32 {
        self.domid
    }

    /// Clone.
    fn clone(&self) -> Self {
        Clone::clone(self)
    }
}

/// Xen Grant memory mapping interface.

const XEN_GRANT_ADDR_OFF: u64 = 1 << 63;

#[repr(C)]
#[derive(Debug, Copy, Clone)]
/// Grant reference
///
/// include/uapi/xen/gntdev.h: `ioctl_gntdev_grant_ref`
struct GntDevGrantRef {
    /// The domain ID of the grant to be mapped.
    domid: u32,
    /// The grant reference of the grant to be mapped.
    r#ef: u32,
}

#[repr(C)]
#[derive(Debug)]
/// Grant dev mapping reference
///
/// include/uapi/xen/gntdev.h: `ioctl_gntdev_map_grant_ref`
struct GntDevMapGrantRef {
    /// The number of grants to be mapped.
    count: u32,
    /// Unused padding
    pad: u32,
    /// The offset to be used on a subsequent call to mmap().
    index: u64,
    /// Array of grant references, of size @count.
    refs: [GntDevGrantRef; 0],
}

impl GntDevMapGrantRef {
    fn layout(count: usize) -> Layout {
        let size = size_of::<Self>() + count * size_of::<GntDevGrantRef>();
        Layout::from_size_align(size, align_of::<Self>()).unwrap()
    }

    fn new(domid: u32, base: u32, count: usize) -> &'static mut GntDevMapGrantRef {
        let layout = Self::layout(count);

        // SAFETY: This is safe as we are allocating a fixed size of memory that needs to be passed
        // to the ioctl later.
        let (map, refs) = unsafe {
            let ptr = alloc::alloc(layout);
            if ptr.is_null() {
                handle_alloc_error(layout);
            }

            let map: &mut GntDevMapGrantRef = &mut *(ptr as *mut GntDevMapGrantRef);
            let refs: &mut [GntDevGrantRef] = slice::from_raw_parts_mut(
                ptr.add(size_of::<GntDevMapGrantRef>()) as *mut GntDevGrantRef,
                count,
            );

            (map, refs)
        };

        map.count = count as u32;
        map.pad = 0;
        map.index = 0;

        for (i, r) in refs.iter_mut().enumerate().take(count) {
            r.domid = domid;
            r.r#ef = base + i as u32;
        }

        map
    }
}

impl Drop for GntDevMapGrantRef {
    fn drop(&mut self) {
        // SAFETY: This is safe because we mapped the ptr earlier.
        unsafe { alloc::dealloc(self as *mut _ as *mut u8, Self::layout(self.count as usize)) }
    }
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
/// Grant dev un-mapping reference
///
/// include/uapi/xen/gntdev.h: `ioctl_gntdev_unmap_grant_ref`
struct GntDevUnmapGrantRef {
    /// The offset returned by the map operation.
    index: u64,
    /// The number of grants to be unmapped.
    count: u32,
    /// Unused padding
    pad: u32,
}

const XEN_GNTDEV_TYPE: u32 = 'G' as u32;

// #define IOCTL_GNTDEV_MAP_GRANT_REF _IOC(_IOC_NONE, 'G', 0, sizeof(ioctl_gntdev_map_grant_ref))
fn ioctl_gntdev_map_grant_ref() -> c_ulong {
    ioctl_expr(
        _IOC_NONE,
        XEN_GNTDEV_TYPE,
        0,
        (size_of::<GntDevMapGrantRef>() + size_of::<GntDevGrantRef>()) as u32,
    )
}

// #define IOCTL_GNTDEV_UNMAP_GRANT_REF _IOC(_IOC_NONE, 'G', 1, sizeof(struct ioctl_gntdev_unmap_grant_ref))
fn ioctl_gntdev_unmap_grant_ref() -> c_ulong {
    ioctl_expr(
        _IOC_NONE,
        XEN_GNTDEV_TYPE,
        1,
        size_of::<GntDevUnmapGrantRef>() as u32,
    )
}

/// Trait implemented by underlying `MmapRegion`.
#[derive(Debug)]
pub(crate) struct MappedAddressXenGrant {
    grant: MmapXenGrant,
    unmap_addr: *mut u8,
    size: usize,
    offset: usize,
    index: u64,
}

impl MappedAddress for MappedAddressXenGrant {
    /// Mapped address for the region.
    fn offset(&self) -> usize {
        self.offset
    }
}

impl MappedAddressXenGrant {
    fn new(grant: MmapXenGrant, size: usize, prot: i32, offset: usize) -> Result<Self> {
        let page_size = page_size() as usize;
        let page_base: usize = (offset / page_size) * page_size;
        let page_off = offset - page_base;
        let size = page_off + size;

        let addr = grant.guest_base.0 + page_base as u64;
        let (unmap_addr, index) = grant.mmap_common(GuestAddress(addr), size, prot)?;

        // We may map from anywhere in the region, calculate address again to make sure offset
        // remains valid.
        *grant.addr.lock().unwrap() = (unmap_addr as usize - page_base) as *mut u8;

        Ok(Self {
            grant,
            unmap_addr,
            size,
            offset,
            index,
        })
    }
}

impl Drop for MappedAddressXenGrant {
    fn drop(&mut self) {
        self.grant
            .munmap_common(self.unmap_addr, self.size, self.index);
    }
}

#[derive(Clone, Debug)]
/// Xen foreign memory specific mmap() implementation.
pub struct MmapXenGrant {
    addr: Arc<Mutex<*mut u8>>,
    guest_base: GuestAddress,
    flags: i32,
    fd: i32,
    size: usize,
    index: u64,
    xen_flags: u32,
    domid: u32,
}

impl MmapXenGrant {
    /// Create a new object.
    pub fn new_with(domid: u32, guest_base: GuestAddress, xen_flags: u32) -> Result<Self> {
        let map = Self {
            addr: Arc::new(Mutex::new(null_mut())),
            guest_base,
            flags: 0,
            fd: 0,
            size: 0,
            index: 0,
            xen_flags: xen_flags | MmapXenFlags::GRANT.bits(),
            domid,
        };

        if MmapXenFlags::is_valid(map.xen_flags) {
            Ok(map)
        } else {
            Err(Error::XenMmapFlags(map.xen_flags))
        }
    }

    // Can mmap entire region in advance.
    fn mmap_in_advance(&self) -> bool {
        MmapXenFlags::mmap_in_advance(self.xen_flags)
    }

    fn mmap_ioctl(&self, guest_base: GuestAddress, count: usize) -> Result<u64> {
        let base = ((guest_base.0 & !XEN_GRANT_ADDR_OFF) / page_size()) as u32;
        let map = GntDevMapGrantRef::new(self.domid, base, count);

        // SAFETY: This is safe because the ioctl guarantees to not access memory beyond ptr.
        let ret = unsafe { ioctl_with_ref(self, ioctl_gntdev_map_grant_ref(), map) };

        if ret == 0 {
            Ok(map.index)
        } else {
            Err(Error::Mmap(io::Error::last_os_error()))
        }
    }

    fn unmap_ioctl(&self, count: u32, index: u64) -> Result<()> {
        let unmap = GntDevUnmapGrantRef {
            index,
            count,
            pad: 0,
        };

        // SAFETY: This is safe because the ioctl guarantees to not access memory beyond unmap.
        let ret = unsafe { ioctl_with_ref(self, ioctl_gntdev_unmap_grant_ref(), &unmap) };

        if ret == 0 {
            Ok(())
        } else {
            Err(Error::Mmap(io::Error::last_os_error()))
        }
    }

    fn mmap_common(
        &self,
        guest_base: GuestAddress,
        size: usize,
        prot: i32,
    ) -> Result<(*mut u8, u64)> {
        let (count, size) = pages(size);
        let index = self.mmap_ioctl(guest_base, count)?;
        let addr = mmap_unix::mmap(size, prot, self.flags, self.fd, index as i64)?;

        Ok((addr, index))
    }

    // Unmaps the memory in architecture / platform dependent way.
    fn munmap_common(&self, unmap_addr: *mut u8, size: usize, index: u64) {
        let (count, size) = pages(size);

        // SAFETY: This is safe because we mapped the addr earlier.
        unsafe {
            libc::munmap(unmap_addr as *mut c_void, size);
        }

        self.unmap_ioctl(count as u32, index).unwrap();
    }
}

impl AsRawFd for MmapXenGrant {
    fn as_raw_fd(&self) -> i32 {
        self.fd
    }
}

impl MmapInternal for MmapXenGrant {
    /// Mapped address for the region.
    fn addr(&self) -> *mut u8 {
        *self.addr.lock().unwrap()
    }

    /// Set mapped address for the region.
    fn set_addr(&mut self, addr: *mut u8) -> Result<()> {
        // Mapping with raw pointer isn't allowed with no-advance-mapping.
        if !self.mmap_in_advance() {
            return Err(Error::SetAddr(addr));
        }

        *self.addr.lock().unwrap() = addr;
        Ok(())
    }

    /// Maps the memory in architecture / platform dependent way.
    fn mmap(
        &mut self,
        size: usize,
        prot: i32,
        flags: i32,
        file_offset: &Option<FileOffset>,
    ) -> Result<()> {
        let (fd, f_off) = if let Some(ref f_off) = file_offset {
            (f_off.file().as_raw_fd(), f_off.start())
        } else {
            (-1, 0)
        };

        if f_off != 0 {
            return Err(Error::InvalidOffsetLength);
        }

        self.fd = fd;
        self.flags = flags;

        // Region can't be mapped in advance, partial mapping will be done later.
        if !self.mmap_in_advance() {
            return Ok(());
        }

        (*self.addr.lock().unwrap(), self.index) = self.mmap_common(self.guest_base, size, prot)?;
        self.size = size;
        Ok(())
    }

    /// Returns the mapped address corresponding to offset.
    fn translate(
        &self,
        size: usize,
        is_read: bool,
        offset: usize,
    ) -> Result<Box<dyn MappedAddress>> {
        // Already mapped earlier.
        if self.mmap_in_advance() {
            Ok(Box::new(MappedAddressSimple::new(offset)))
        } else {
            let prot = if is_read { PROT_READ } else { PROT_WRITE };

            Ok(Box::new(MappedAddressXenGrant::new(
                MmapInternal::clone(self),
                size,
                prot,
                offset,
            )?))
        }
    }

    /// Unmaps the memory in architecture / platform dependent way.
    fn munmap(&self) {
        if self.mmap_in_advance() {
            self.munmap_common(*self.addr.lock().unwrap(), self.size, self.index);
        }
    }

    /// Mmap specific flags.
    fn mmap_flags(&self) -> u32 {
        self.xen_flags
    }

    /// Mmap specific data.
    fn mmap_data(&self) -> u32 {
        self.domid
    }

    /// Clone.
    fn clone(&self) -> Self {
        Clone::clone(self)
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::undocumented_unsafe_blocks)]
    use super::*;

    use vmm_sys_util::tempfile::TempFile;

    type MmapRegion = crate::MmapRegion<()>;

    #[test]
    fn test_foreign_map_failures() {
        let addr = GuestAddress(0x1000);
        let domid = 1;

        // Failures
        let r = MmapXenForeign::new_with(domid, addr, MmapXenFlags::GRANT.bits());
        assert_eq!(
            format!("{:?}", r.unwrap_err()),
            format!("XenMmapFlags({:x})", MmapXenFlags::ALL.bits()),
        );

        let r = MmapXenForeign::new_with(domid, addr, MmapXenFlags::NO_ADVANCE_MAP.bits());
        assert_eq!(
            format!("{:?}", r.unwrap_err()),
            format!(
                "XenMmapFlags({:x})",
                MmapXenFlags::NO_ADVANCE_MAP.bits() | MmapXenFlags::FOREIGN.bits(),
            ),
        );

        // Success
        let map = MmapXenForeign::new_with(domid, addr, 0).unwrap();
        let f = TempFile::new().unwrap().into_file();
        let f_off = FileOffset::new(f, 0);
        assert!(MmapRegion::from_file(map, f_off, 0x1000).is_err());
    }

    #[test]
    fn test_foreign_map_ioctl_failure() {
        let addr = GuestAddress(0x1000);
        let domid = 1;
        let mut map = MmapXenForeign::new_with(domid, addr, 0).unwrap();
        let file = TempFile::new().unwrap().into_file();
        map.fd = file.as_raw_fd();
        assert!(map.mmap_ioctl(0x1000, null_mut()).is_err());
    }

    #[test]
    fn test_foreign_map() {
        let addr = GuestAddress(0x1000);
        let domid = 1;

        let mut map = MmapXenForeign::new_with(domid, addr, 0).unwrap();

        assert_eq!(map.domid, domid);
        assert_eq!(map.guest_base, addr);
        assert_eq!(map.xen_flags, MmapXenFlags::FOREIGN.bits());
        assert_eq!(map.addr, None);
        assert_eq!(map.size, 0);
        assert_eq!(map.fd, 0);

        let vaddr = 0xBA000000 as *mut u8;
        map.set_addr(vaddr).unwrap();
        assert_eq!(map.addr(), vaddr);

        assert_eq!(map.mmap_flags(), MmapXenFlags::FOREIGN.bits());
        assert_eq!(map.mmap_data(), domid);
        assert_eq!(MmapInternal::clone(&map), map);

        let offset = 0x120;
        assert_eq!(
            map.translate(0x1000, true, offset).unwrap().offset(),
            offset,
        );
    }

    #[test]
    fn test_grant_map_failures() {
        let addr = GuestAddress(0x1000);
        let domid = 1;

        // Failures
        let r = MmapXenGrant::new_with(domid, addr, MmapXenFlags::FOREIGN.bits());
        assert_eq!(
            format!("{:?}", r.unwrap_err()),
            format!("XenMmapFlags({:x})", MmapXenFlags::ALL.bits()),
        );

        // Success
        let map = MmapXenGrant::new_with(domid, addr, 0).unwrap();
        let f = TempFile::new().unwrap().into_file();
        let f_off = FileOffset::new(f, 0);
        assert!(MmapRegion::from_file(map, f_off, 0x1000).is_err());
    }

    #[test]
    fn test_grant_map_ioctl_failure() {
        let addr = GuestAddress(0x1000);
        let domid = 1;
        let mut map =
            MmapXenGrant::new_with(domid, addr, MmapXenFlags::NO_ADVANCE_MAP.bits()).unwrap();
        let file = TempFile::new().unwrap().into_file();
        map.fd = file.as_raw_fd();
        assert!(map.mmap_ioctl(addr, 0x1000).is_err());

        let offset = 0x120;
        assert!(map.translate(0x1000, true, offset).is_err());
    }

    #[test]
    fn test_grant_map() {
        let addr = GuestAddress(0x1000);
        let domid = 1;
        let flag = MmapXenFlags::NO_ADVANCE_MAP.bits();

        let mut map = MmapXenGrant::new_with(domid, addr, flag).unwrap();

        assert_eq!(map.guest_base, addr);
        assert_eq!(map.flags, 0);
        assert_eq!(map.fd, 0);
        assert_eq!(map.size, 0);
        assert_eq!(map.index, 0);
        assert_eq!(map.xen_flags, flag | MmapXenFlags::GRANT.bits());
        assert_eq!(map.domid, domid);

        let vaddr = 0xBA000000 as *mut u8;
        let r = map.set_addr(vaddr);
        assert_eq!(
            format!("{:?}", r.unwrap_err()),
            format!("SetAddr({:x?})", vaddr),
        );

        assert_eq!(map.mmap_flags(), flag | MmapXenFlags::GRANT.bits());
        assert_eq!(map.mmap_data(), domid);
        assert!(!map.mmap_in_advance());

        let mut map = MmapXenGrant::new_with(domid, addr, 0).unwrap();
        map.set_addr(vaddr).unwrap();
        assert!(map.mmap_in_advance());

        let offset = 0x120;
        assert_eq!(
            map.translate(0x1000, true, offset).unwrap().offset(),
            offset,
        );
    }

    #[test]
    fn test_grant_ref_alloc() {
        let r = GntDevMapGrantRef::new(0, 0x1000, 0x100);
        assert_eq!(r.count, 0x100);
        assert_eq!(r.pad, 0);
        assert_eq!(r.index, 0);
    }
}
