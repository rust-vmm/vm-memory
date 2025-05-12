// Copyright (C) 2025 Red Hat. All rights reserved.
//
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Provides a trait for virtual I/O memory.
//!
//! This trait is more stripped down than `GuestMemory` because the fragmented nature of virtual
//! memory does not allow a direct translation to long continuous regions.
//!
//! In addition, any access to virtual memory must be annotated with the intended access mode (i.e.
//! reading and/or writing).

use crate::guest_memory::Result;
use crate::{bitmap, GuestAddress, GuestMemory, MemoryRegionAddress, VolatileSlice};

/// Permissions for accessing virtual memory.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum Permissions {
    /// No permissions
    No = 0b00,
    /// Read-only
    Read = 0b01,
    /// Write-only
    Write = 0b10,
    /// Allow both reading and writing
    ReadWrite = 0b11,
}

impl Permissions {
    /// Convert the numerical representation into the enum.
    ///
    /// # Panics
    ///
    /// Panics if `raw` is not a valid representation of any `Permissions` variant.
    fn from_repr(raw: u8) -> Self {
        use Permissions::*;

        match raw {
            value if value == No as u8 => No,
            value if value == Read as u8 => Read,
            value if value == Write as u8 => Write,
            value if value == ReadWrite as u8 => ReadWrite,
            _ => panic!("{raw:x} is not a valid raw Permissions value"),
        }
    }

    /// Check whether the permissions `self` allow the given `access`.
    pub fn allow(&self, access: Self) -> bool {
        *self & access == access
    }
}

impl std::ops::BitOr for Permissions {
    type Output = Permissions;

    /// Return the union of `self` and `rhs`.
    fn bitor(self, rhs: Permissions) -> Self::Output {
        Self::from_repr(self as u8 | rhs as u8)
    }
}

impl std::ops::BitAnd for Permissions {
    type Output = Permissions;

    /// Return the intersection of `self` and `rhs`.
    fn bitand(self, rhs: Permissions) -> Self::Output {
        Self::from_repr(self as u8 & rhs as u8)
    }
}

/// Represents virtual I/O memory.
///
/// `IoMemory` is generally backed by some “physical” `GuestMemory`, which then consists for
/// `GuestMemoryRegion` objects.  However, the mapping from I/O virtual addresses (IOVAs) to
/// physical addresses may be arbitrarily fragmented.  Translation is done via an IOMMU.
///
/// Note in contrast to `GuestMemory`:
/// - Any IOVA range may consist of arbitrarily many underlying ranges in physical memory.
/// - Accessing an IOVA requires passing the intended access mode, and the IOMMU will check whether
///   the given access mode is permitted for the given IOVA.
/// - The translation result for a given IOVA may change over time (i.e. the physical address
///   associated with an IOVA may change).
pub trait IoMemory {
    /// Underlying `GuestMemory` type.
    type PhysicalMemory: GuestMemory + ?Sized;

    /// Return `true` if `addr..(addr + count)` is accessible with `access`.
    fn range_accessible(&self, addr: GuestAddress, count: usize, access: Permissions) -> bool;

    /// Invokes callback `f` to handle data in the address range `[addr, addr + count)`, with
    /// permissions `access`.
    ///
    /// The address range `[addr, addr + count)` may span more than a single page in virtual
    /// memory, and more than one [`GuestMemoryRegion`](trait.GuestMemoryRegion.html) object, or
    /// even have holes or non-accessible regions in it.  So `f` is invoked for each
    /// [`GuestMemoryRegion`](trait.GuestMemoryRegion.html) object and each non-continuous page
    /// involved, and then this function returns:
    /// - the error code returned by the callback 'f'
    /// - the size of the already handled data when encountering the first hole
    /// - the size of the already handled data when the whole range has been handled
    ///
    /// The parameters to `f` are, in order:
    /// - Offset inside of the whole range (i.e. `addr` corresponds to offset `0`),
    /// - Length of the current chunk in bytes,
    /// - Relative address inside the [`GuestMemoryRegion`],
    /// - The underlying [`GuestMemoryRegion`].
    ///
    /// `f` should return the number of bytes it handled.  That number may be less than the length
    /// passed to it, in which case it will be called again for the chunk following immediately
    /// after that returned length.  If `f` returns 0, processing will be stopped.
    fn try_access<F>(
        &self,
        count: usize,
        addr: GuestAddress,
        access: Permissions,
        f: F,
    ) -> Result<usize>
    where
        F: FnMut(
            usize,
            usize,
            MemoryRegionAddress,
            &<Self::PhysicalMemory as GuestMemory>::R,
        ) -> Result<usize>;

    /// Returns a [`VolatileSlice`](struct.VolatileSlice.html) of `count` bytes starting at
    /// `addr`.
    ///
    /// Note that because of the fragmented nature of virtual memory, it can easily happen that the
    /// range `[addr, addr + count)` is not backed by a continuous region in our own virtual
    /// memory, which will make generating the slice impossible.
    fn get_slices<'a>(
        &'a self,
        addr: GuestAddress,
        count: usize,
        access: Permissions,
    ) -> Result<impl Iterator<Item = Result<VolatileSlice<'a, bitmap::MS<'a, Self::PhysicalMemory>>>>>;

    /// If this virtual memory is just a plain `GuestMemory` object underneath without an IOMMU
    /// translation layer in between, return that `GuestMemory` object.
    fn physical_memory(&self) -> Option<&Self::PhysicalMemory> {
        None
    }
}

/// Allow accessing every [`GuestMemory`] via [`IoMemory`].
///
/// [`IoMemory`] is a generalization of [`GuestMemory`]: Every object implementing the former is a
/// subset of an object implementing the latter (there always is an underlying [`GuestMemory`]),
/// with an opaque internal mapping on top, e.g. provided by an IOMMU.
///
/// Every [`GuestMemory`] is therefore trivially also an [`IoMemory`], assuming a complete identity
/// mapping (which we must assume, so that accessing such objects via either trait will yield the
/// same result): Basically, all [`IoMemory`] methods are implemented as trivial wrappers around
/// the same [`GuestMemory`] methods (if available), discarding the `access` parameter.
impl<M: GuestMemory + ?Sized> IoMemory for M {
    type PhysicalMemory = M;

    fn range_accessible(&self, addr: GuestAddress, count: usize, _access: Permissions) -> bool {
        if let Ok(done) = <M as GuestMemory>::try_access(self, count, addr, |_, len, _, _| Ok(len))
        {
            done == count
        } else {
            false
        }
    }

    fn try_access<F>(
        &self,
        count: usize,
        addr: GuestAddress,
        _access: Permissions,
        f: F,
    ) -> Result<usize>
    where
        F: FnMut(
            usize,
            usize,
            MemoryRegionAddress,
            &<Self::PhysicalMemory as GuestMemory>::R,
        ) -> Result<usize>,
    {
        <M as GuestMemory>::try_access(self, count, addr, f)
    }

    fn get_slices<'a>(
        &'a self,
        addr: GuestAddress,
        count: usize,
        _access: Permissions,
    ) -> Result<impl Iterator<Item = Result<VolatileSlice<'a, bitmap::MS<'a, Self::PhysicalMemory>>>>>
    {
        Ok(<M as GuestMemory>::get_slices(self, addr, count))
    }

    fn physical_memory(&self) -> Option<&Self::PhysicalMemory> {
        Some(self)
    }
}
