// Copyright 2023 Linaro Ltd. All Rights Reserved.
//          Viresh Kumar <viresh.kumar@linaro.org>
//
// Xen specific memory mapping implementations
//
// SPDX-License-Identifier: Apache-2.0 or BSD-3-Clause

//! Helper structure for working with mmap'ed memory regions on Xen.

use bitflags::bitflags;
use libc::{c_int, c_void, MAP_SHARED, _SC_PAGESIZE};
use std::{io, mem::size_of, os::raw::c_ulong, os::unix::io::AsRawFd, ptr::null_mut};

use vmm_sys_util::{
    fam::{Error as FamError, FamStruct, FamStructWrapper},
    generate_fam_struct_impl,
    ioctl::{ioctl_expr, ioctl_with_ref, _IOC_NONE},
};

use crate::guest_memory::{FileOffset, GuestAddress};
use crate::mmap_unix::{Error, Mmap as MmapUnix, Result};

/// Error conditions that may arise with Xen APIs.
#[derive(Debug, thiserror::Error)]
pub enum XenError {
    /// Invalid Xen mmap flags.
    #[error("Invalid Xen Mmap flags: {0:x}")]
    MmapFlags(u32),
    /// Fam error.
    #[error("Fam error: {0}")]
    Fam(FamError),
}

fn page_size() -> u64 {
    // SAFETY: Safe because this call just returns the page size and doesn't have any side effects.
    unsafe { libc::sysconf(_SC_PAGESIZE) as u64 }
}

fn pages(size: usize) -> (usize, usize) {
    let page_size = page_size() as usize;
    let num = (size + page_size - 1) / page_size;

    (num, page_size * num)
}

fn validate_file(file_offset: &Option<FileOffset>) -> Result<(i32, u64)> {
    let (fd, f_offset) = match file_offset {
        Some(file) => (file.file().as_raw_fd(), file.start()),
        None => return Err(Error::InvalidFileOffset),
    };

    // We don't allow file offsets with Xen foreign mappings.
    if f_offset != 0 {
        return Err(Error::InvalidOffsetLength);
    }

    Ok((fd, f_offset))
}

// Bit mask for the vhost-user xen mmap message.
bitflags! {
    /// Flags for the Xen mmap message.
    pub struct MmapXenFlags: u32 {
        /// Standard Unix memory mapping.
        const UNIX = 0x0;
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
    pub fn is_valid(&self) -> bool {
        // Only one of UNIX, FOREIGN or GRANT should be set and mmap_in_advance() should be true
        // with FOREIGN and UNIX.
        if self.is_grant() {
            !self.is_foreign()
        } else if self.is_foreign() || self.is_unix() {
            self.mmap_in_advance()
        } else {
            false
        }
    }

    /// Is standard Unix memory.
    pub fn is_unix(&self) -> bool {
        self.bits() == Self::UNIX.bits()
    }

    /// Is xen foreign memory.
    pub fn is_foreign(&self) -> bool {
        self.contains(Self::FOREIGN)
    }

    /// Is xen grant memory.
    pub fn is_grant(&self) -> bool {
        self.contains(Self::GRANT)
    }

    /// Can mmap entire region in advance.
    pub fn mmap_in_advance(&self) -> bool {
        !self.contains(Self::NO_ADVANCE_MAP)
    }
}

// Xen Foreign memory mapping interface.
trait MmapXenTrait: std::fmt::Debug {
    #[cfg(test)]
    fn owned(&self) -> bool {
        true
    }

    fn mmap(
        &mut self,
        size: usize,
        prot: i32,
        flags: i32,
        file_offset: &Option<FileOffset>,
    ) -> Result<()>;

    #[allow(unused_variables)]
    fn mmap_slice(&self, addr: *const u8, prot: i32, len: usize) -> Result<MmapXenSlice> {
        panic!();
    }

    fn addr(&self) -> *mut u8;

    fn mmap_in_advance(&self) -> bool;

    fn raw_mmap(&mut self, _addr: *mut u8) {
        panic!();
    }
}

// Standard Unix memory mapping.
#[derive(Clone, Debug, PartialEq)]
struct MmapXenUnix(Option<MmapUnix>);

impl MmapXenUnix {
    fn new() -> Self {
        Self(None)
    }
}

impl MmapXenTrait for MmapXenUnix {
    fn mmap(
        &mut self,
        size: usize,
        prot: i32,
        flags: i32,
        file_offset: &Option<FileOffset>,
    ) -> Result<()> {
        self.0 = Some(MmapUnix::with_checks(size, prot, flags, file_offset)?);
        Ok(())
    }

    fn addr(&self) -> *mut u8 {
        if let Some(ref mmap) = self.0 {
            mmap.addr()
        } else {
            null_mut()
        }
    }

    fn raw_mmap(&mut self, addr: *mut u8) {
        self.0 = Some(MmapUnix::raw(addr));
    }

    fn mmap_in_advance(&self) -> bool {
        self.0.as_ref().unwrap().mmap_in_advance()
    }

    #[cfg(test)]
    fn owned(&self) -> bool {
        self.0.as_ref().unwrap().owned()
    }
}

// Privcmd mmap batch v2 command
//
// include/uapi/xen/privcmd.h: `privcmd_mmapbatch_v2`
#[repr(C)]
#[derive(Debug, Copy, Clone)]
struct PrivCmdMmapBatchV2 {
    // number of pages to populate
    num: u32,
    // target domain
    domid: u16,
    // virtual address
    addr: *mut c_void,
    // array of mfns
    arr: *const u64,
    // array of error codes
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

// Xen foreign memory specific implementation.
#[derive(Clone, Debug, PartialEq)]
struct MmapXenForeign {
    domid: u32,
    guest_base: GuestAddress,
    mmap: Option<MmapUnix>,
    fd: i32,
}

impl AsRawFd for MmapXenForeign {
    fn as_raw_fd(&self) -> i32 {
        self.fd
    }
}

impl MmapXenForeign {
    fn new(domid: u32, guest_base: GuestAddress) -> Self {
        Self {
            domid,
            guest_base,
            mmap: None,
            fd: 0,
        }
    }

    // Ioctl to pass additional information to mmap infrastructure of privcmd driver.
    fn ioctl(&self, count: usize, addr: *mut u8) -> Result<()> {
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

        // SAFETY: This is safe because the ioctl guarantees to not access memory beyond `map`.
        let ret = unsafe { ioctl_with_ref(self, ioctl_privcmd_mmapbatch_v2(), &map) };

        if ret == 0 {
            Ok(())
        } else {
            Err(Error::Mmap(io::Error::last_os_error()))
        }
    }
}

impl MmapXenTrait for MmapXenForeign {
    // Maps the entire guest memory space at once.
    fn mmap(
        &mut self,
        size: usize,
        prot: i32,
        flags: i32,
        file_offset: &Option<FileOffset>,
    ) -> Result<()> {
        let (fd, f_offset) = validate_file(file_offset)?;
        let (count, size) = pages(size);
        let mmap = MmapUnix::new(size, prot, flags | MAP_SHARED, fd, f_offset)?;

        self.fd = fd;
        self.ioctl(count, mmap.addr())?;
        self.mmap = Some(mmap);

        Ok(())
    }

    fn addr(&self) -> *mut u8 {
        if let Some(ref mmap) = self.mmap {
            mmap.addr()
        } else {
            null_mut()
        }
    }

    fn mmap_in_advance(&self) -> bool {
        true
    }
}

// Xen Grant memory mapping interface.

const XEN_GRANT_ADDR_OFF: u64 = 1 << 63;

// Grant reference
//
// include/uapi/xen/gntdev.h: `ioctl_gntdev_grant_ref`
#[repr(C)]
#[derive(Copy, Clone, Debug, Default, PartialEq)]
struct GntDevGrantRef {
    // The domain ID of the grant to be mapped.
    domid: u32,
    // The grant reference of the grant to be mapped.
    reference: u32,
}

#[repr(C)]
#[derive(Debug, Default, PartialEq, Eq)]
struct __IncompleteArrayField<T>(::std::marker::PhantomData<T>, [T; 0]);
impl<T> __IncompleteArrayField<T> {
    #[inline]
    pub unsafe fn as_ptr(&self) -> *const T {
        self as *const __IncompleteArrayField<T> as *const T
    }
    #[inline]
    pub unsafe fn as_mut_ptr(&mut self) -> *mut T {
        self as *mut __IncompleteArrayField<T> as *mut T
    }
    #[inline]
    pub unsafe fn as_slice(&self, len: usize) -> &[T] {
        ::std::slice::from_raw_parts(self.as_ptr(), len)
    }
    #[inline]
    pub unsafe fn as_mut_slice(&mut self, len: usize) -> &mut [T] {
        ::std::slice::from_raw_parts_mut(self.as_mut_ptr(), len)
    }
}

// Grant dev mapping reference
//
// include/uapi/xen/gntdev.h: `ioctl_gntdev_map_grant_ref`
#[repr(C)]
#[derive(Debug, Default)]
struct GntDevMapGrantRef {
    // The number of grants to be mapped.
    count: u32,
    // Unused padding
    pad: u32,
    // The offset to be used on a subsequent call to mmap().
    index: u64,
    // Array of grant references, of size @count.
    refs: __IncompleteArrayField<GntDevGrantRef>,
}

generate_fam_struct_impl!(
    GntDevMapGrantRef,
    GntDevGrantRef,
    refs,
    u32,
    count,
    usize::MAX
);

type GntDevMapGrantRefWrapper = FamStructWrapper<GntDevMapGrantRef>;

impl GntDevMapGrantRef {
    fn new(domid: u32, base: u32, count: usize) -> Result<GntDevMapGrantRefWrapper> {
        let mut wrapper = GntDevMapGrantRefWrapper::new(count)
            .map_err(XenError::Fam)
            .map_err(Error::Xen)?;
        let refs = wrapper.as_mut_slice();

        // GntDevMapGrantRef's pad and index are initialized to 0 by Fam layer.
        for (i, r) in refs.iter_mut().enumerate().take(count) {
            r.domid = domid;
            r.reference = base + i as u32;
        }

        Ok(wrapper)
    }
}

// Grant dev un-mapping reference
//
// include/uapi/xen/gntdev.h: `ioctl_gntdev_unmap_grant_ref`
#[repr(C)]
#[derive(Debug, Copy, Clone)]
struct GntDevUnmapGrantRef {
    // The offset returned by the map operation.
    index: u64,
    // The number of grants to be unmapped.
    count: u32,
    // Unused padding
    pad: u32,
}

impl GntDevUnmapGrantRef {
    fn new(index: u64, count: u32) -> Self {
        Self {
            index,
            count,
            pad: 0,
        }
    }
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

// Xen grant memory specific implementation.
#[derive(Clone, Debug, PartialEq)]
struct MmapXenGrant {
    guest_base: GuestAddress,
    mmap: Option<MmapUnix>,
    flags: i32,
    fd: i32,
    size: usize,
    index: u64,
    domid: u32,
    mmap_in_advance: bool,
}

impl AsRawFd for MmapXenGrant {
    fn as_raw_fd(&self) -> i32 {
        self.fd
    }
}

impl MmapXenGrant {
    fn new(domid: u32, guest_base: GuestAddress, flags: MmapXenFlags) -> Self {
        Self {
            guest_base,
            mmap: None,
            flags: 0,
            fd: 0,
            size: 0,
            index: 0,
            domid,
            mmap_in_advance: flags.mmap_in_advance(),
        }
    }

    fn mmap_ioctl(&self, addr: GuestAddress, count: usize) -> Result<u64> {
        let base = ((addr.0 & !XEN_GRANT_ADDR_OFF) / page_size()) as u32;
        let wrapper = GntDevMapGrantRef::new(self.domid, base, count)?;
        let reference = wrapper.as_fam_struct_ref();

        // SAFETY: This is safe because the ioctl guarantees to not access memory beyond reference.
        let ret = unsafe { ioctl_with_ref(self, ioctl_gntdev_map_grant_ref(), reference) };

        if ret == 0 {
            Ok(reference.index)
        } else {
            Err(Error::Mmap(io::Error::last_os_error()))
        }
    }

    fn unmap_ioctl(&self, count: u32, index: u64) -> Result<()> {
        let unmap = GntDevUnmapGrantRef::new(index, count);

        // SAFETY: This is safe because the ioctl guarantees to not access memory beyond unmap.
        let ret = unsafe { ioctl_with_ref(self, ioctl_gntdev_unmap_grant_ref(), &unmap) };

        if ret == 0 {
            Ok(())
        } else {
            Err(Error::Mmap(io::Error::last_os_error()))
        }
    }

    fn mmap_range(&self, addr: GuestAddress, size: usize, prot: i32) -> Result<(MmapUnix, u64)> {
        let (count, size) = pages(size);
        let index = self.mmap_ioctl(addr, count)?;
        let mmap = MmapUnix::new(size, prot, self.flags, self.fd, index)?;

        Ok((mmap, index))
    }

    fn unmap_range(&self, mmap: MmapUnix, size: usize, index: u64) {
        let (count, _) = pages(size);

        // Unmap the address first.
        drop(mmap);
        self.unmap_ioctl(count as u32, index).unwrap();
    }
}

impl MmapXenTrait for MmapXenGrant {
    // Maps the memory if mmap_in_advance() is set.
    fn mmap(
        &mut self,
        size: usize,
        prot: i32,
        flags: i32,
        file_offset: &Option<FileOffset>,
    ) -> Result<()> {
        let (fd, _) = validate_file(file_offset)?;

        // Save fd and flags for later use.
        self.fd = fd;
        self.flags = flags;

        // Region can't be mapped in advance, partial mapping will be done later via
        // `MmapXenSlice`.
        if self.mmap_in_advance() {
            let (mmap, index) = self.mmap_range(self.guest_base, size, prot)?;
            self.mmap = Some(mmap);
            self.index = index;
            self.size = size;
        }

        Ok(())
    }

    // Maps a slice out of the entire region.
    fn mmap_slice(&self, addr: *const u8, prot: i32, len: usize) -> Result<MmapXenSlice> {
        assert!(!self.mmap_in_advance());
        MmapXenSlice::new_with(self.clone(), addr as usize, prot, len)
    }

    fn addr(&self) -> *mut u8 {
        if let Some(ref mmap) = self.mmap {
            mmap.addr()
        } else {
            null_mut()
        }
    }

    fn mmap_in_advance(&self) -> bool {
        self.mmap_in_advance
    }
}

impl Drop for MmapXenGrant {
    fn drop(&mut self) {
        if let Some(mmap) = self.mmap.take() {
            self.unmap_range(mmap, self.size, self.index);
        }
    }
}

#[derive(Debug)]
pub(crate) struct MmapXenSlice {
    grant: Option<MmapXenGrant>,
    mmap: Option<MmapUnix>,
    addr: *mut u8,
    size: usize,
    index: u64,
}

impl MmapXenSlice {
    pub fn new(addr: *mut u8) -> Self {
        Self {
            grant: None,
            mmap: None,
            addr,
            size: 0,
            index: 0,
        }
    }

    fn new_with(grant: MmapXenGrant, offset: usize, prot: i32, size: usize) -> Result<Self> {
        let page_size = page_size() as usize;
        let page_base: usize = (offset / page_size) * page_size;
        let offset = offset - page_base;
        let size = offset + size;

        let addr = grant.guest_base.0 + page_base as u64;
        let (mmap, index) = grant.mmap_range(GuestAddress(addr), size, prot)?;

        // SAFETY: We have already mapped the range including offset.
        let addr = unsafe { mmap.addr().add(offset) };

        Ok(Self {
            grant: Some(grant),
            mmap: Some(mmap),
            addr,
            size,
            index,
        })
    }

    // Mapped address for the region.
    pub fn addr(&self) -> *mut u8 {
        self.addr
    }
}

impl Drop for MmapXenSlice {
    fn drop(&mut self) {
        // Unmaps memory automatically once this instance goes out of scope.
        if let Some(mmap) = self.mmap.take() {
            self.grant
                .as_ref()
                .unwrap()
                .unmap_range(mmap, self.size, self.index);
        }
    }
}

#[derive(Debug)]
pub struct MmapXen {
    xen_flags: MmapXenFlags,
    domid: u32,
    mmap: Box<dyn MmapXenTrait>,
}

impl MmapXen {
    pub fn new(guest_base: GuestAddress, flags: u32, domid: u32) -> Result<Self> {
        let xen_flags = match MmapXenFlags::from_bits(flags) {
            Some(flags) => flags,
            None => return Err(Error::Xen(XenError::MmapFlags(flags))),
        };

        if !xen_flags.is_valid() {
            return Err(Error::Xen(XenError::MmapFlags(xen_flags.bits())));
        }

        Ok(Self {
            xen_flags,
            domid,
            mmap: if xen_flags.is_foreign() {
                Box::new(MmapXenForeign::new(domid, guest_base))
            } else if xen_flags.is_grant() {
                Box::new(MmapXenGrant::new(domid, guest_base, xen_flags))
            } else {
                Box::new(MmapXenUnix::new())
            },
        })
    }

    pub fn addr(&self) -> *mut u8 {
        self.mmap.addr()
    }

    pub fn flags(&self) -> u32 {
        self.xen_flags.bits()
    }

    pub fn data(&self) -> u32 {
        self.domid
    }

    pub fn mmap_in_advance(&self) -> bool {
        self.mmap.mmap_in_advance()
    }

    pub fn raw_mmap(&mut self, addr: *mut u8) {
        self.mmap.raw_mmap(addr);
    }

    pub fn mmap(
        &mut self,
        size: usize,
        prot: i32,
        flags: i32,
        file_offset: &Option<FileOffset>,
    ) -> Result<()> {
        self.mmap.mmap(size, prot, flags, file_offset)
    }

    // Translates the address.
    pub(crate) fn mmap_slice(
        &self,
        addr: *const u8,
        prot: i32,
        len: usize,
    ) -> Result<MmapXenSlice> {
        self.mmap.mmap_slice(addr, prot, len)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    #![allow(clippy::undocumented_unsafe_blocks)]

    use super::*;
    use vmm_sys_util::tempfile::TempFile;

    impl MmapXen {
        pub fn owned(&self) -> bool {
            self.mmap.owned()
        }
    }

    #[test]
    fn test_mmap_xen_failures() {
        let addr = GuestAddress(0x1000);
        let domid = 1;

        // Failures
        let flags = 16;
        let r = MmapXen::new(addr, flags, domid);
        assert_eq!(
            format!("{:?}", r.unwrap_err()),
            format!("Xen(MmapFlags({}))", flags),
        );

        let flag = MmapXenFlags::FOREIGN.bits() | MmapXenFlags::GRANT.bits();
        let r = MmapXen::new(addr, flag, domid);
        assert_eq!(
            format!("{:?}", r.unwrap_err()),
            format!("Xen(MmapFlags({:x}))", MmapXenFlags::ALL.bits()),
        );

        let flag = MmapXenFlags::FOREIGN.bits() | MmapXenFlags::NO_ADVANCE_MAP.bits();
        let r = MmapXen::new(addr, flag, domid);
        assert_eq!(
            format!("{:?}", r.unwrap_err()),
            format!(
                "Xen(MmapFlags({:x}))",
                MmapXenFlags::NO_ADVANCE_MAP.bits() | MmapXenFlags::FOREIGN.bits(),
            ),
        );
    }

    #[test]
    fn test_foreign_map_ioctl_failure() {
        let addr = GuestAddress(0x1000);
        let domid = 1;
        let mut map = MmapXenForeign::new(domid, addr);
        let file = TempFile::new().unwrap().into_file();
        map.fd = file.as_raw_fd();
        assert!(map.ioctl(0x1000, null_mut()).is_err());
    }

    #[test]
    fn test_foreign_map() {
        let addr = GuestAddress(0x1000);
        let domid = 1;

        let map = MmapXenForeign::new(domid, addr);

        assert_eq!(map.domid, domid);
        assert_eq!(map.guest_base, addr);
        assert_eq!(map.addr(), null_mut());
        assert_eq!(map.fd, 0);
        assert!(map.mmap_in_advance());
    }

    #[test]
    fn test_grant_map_ioctl_failure() {
        let addr = GuestAddress(0x1000);
        let domid = 1;
        let flag = MmapXenFlags::NO_ADVANCE_MAP;
        let mut map = MmapXenGrant::new(domid, addr, flag);
        let file = TempFile::new().unwrap().into_file();
        map.fd = file.as_raw_fd();
        assert!(map.mmap_ioctl(addr, 0x1000).is_err());
    }

    #[test]
    fn test_grant_map() {
        let addr = GuestAddress(0x1000);
        let domid = 1;
        let flag = MmapXenFlags::NO_ADVANCE_MAP;
        let map = MmapXenGrant::new(domid, addr, flag);

        assert_eq!(map.guest_base, addr);
        assert_eq!(map.flags, 0);
        assert_eq!(map.fd, 0);
        assert_eq!(map.size, 0);
        assert_eq!(map.index, 0);
        assert_eq!(map.domid, domid);
        assert!(!map.mmap_in_advance());

        let map = MmapXenGrant::new(domid, addr, MmapXenFlags::empty());
        assert!(map.mmap_in_advance());
    }

    #[test]
    fn test_grant_ref_alloc() {
        let wrapper = GntDevMapGrantRef::new(0, 0x1000, 0x100).unwrap();
        let r = wrapper.as_fam_struct_ref();
        assert_eq!(r.count, 0x100);
        assert_eq!(r.pad, 0);
        assert_eq!(r.index, 0);
    }
}
