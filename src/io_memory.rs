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

use crate::bitmap::{self, Bitmap};
use crate::guest_memory::Result;
use crate::{GuestAddress, GuestMemory, GuestMemoryRegion, MemoryRegionAddress, VolatileSlice};

/// Permissions for accessing virtual memory.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Permissions {
    /// No permissions
    No,
    /// Read-only
    Read,
    /// Write-only
    Write,
    /// Allow both reading and writing
    ReadWrite,
}

impl Permissions {
    /// Check whether the permissions `self` allow the given `access`.
    pub fn allow(&self, access: Self) -> bool {
        *self & access == access
    }

    /// Check whether the permissions `self` include write access.
    pub fn has_write(&self) -> bool {
        *self & Permissions::Write == Permissions::Write
    }
}

impl std::ops::BitOr for Permissions {
    type Output = Permissions;

    /// Return the union of `self` and `rhs`.
    fn bitor(self, rhs: Permissions) -> Self::Output {
        use Permissions::*;

        match (self, rhs) {
            (No, rhs) => rhs,
            (lhs, No) => lhs,
            (ReadWrite, _) | (_, ReadWrite) => ReadWrite,
            (Read, Read) => Read,
            (Read, Write) | (Write, Read) => ReadWrite,
            (Write, Write) => Write,
        }
    }
}

impl std::ops::BitAnd for Permissions {
    type Output = Permissions;

    /// Return the intersection of `self` and `rhs`.
    fn bitand(self, rhs: Permissions) -> Self::Output {
        use Permissions::*;

        match (self, rhs) {
            (No, _) | (_, No) => No,
            (ReadWrite, rhs) => rhs,
            (lhs, ReadWrite) => lhs,
            (Read, Read) => Read,
            (Read, Write) | (Write, Read) => No,
            (Write, Write) => Write,
        }
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
    type PhysicalMemory: GuestMemory;
    /// Dirty bitmap type for tracking writes to the IOVA address space.
    type Bitmap: Bitmap;

    /// Return `true` if `addr..(addr + count)` is accessible with `access`.
    fn range_accessible(&self, addr: GuestAddress, count: usize, access: Permissions) -> bool;

    /// Invokes callback `f` to handle data in the address range `[addr, addr + count)`, with
    /// permissions `access`.
    ///
    /// The address range `[addr, addr + count)` may span more than one
    /// [`GuestMemoryRegion`](trait.GuestMemoryRegion.html) object, or even have holes in it.
    /// So [`try_access()`](trait.IoMemory.html#method.try_access) invokes the callback 'f'
    /// for each [`GuestMemoryRegion`](trait.GuestMemoryRegion.html) object involved and returns:
    /// - the error code returned by the callback 'f'
    /// - the size of the already handled data when encountering the first hole
    /// - the size of the already handled data when the whole range has been handled
    fn try_access<'a, F>(
        &'a self,
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
            &'a <Self::PhysicalMemory as GuestMemory>::R,
        ) -> Result<usize>;

    /// Returns a [`VolatileSlice`](struct.VolatileSlice.html) of `count` bytes starting at
    /// `addr`.
    ///
    /// Note that because of the fragmented nature of virtual memory, it can easily happen that the
    /// range `[addr, addr + count)` is not backed by a continuous region in our own virtual
    /// memory, which will make generating the slice impossible.
    fn get_slice(
        &self,
        addr: GuestAddress,
        count: usize,
        access: Permissions,
    ) -> Result<VolatileSlice<bitmap::BS<Self::Bitmap>>>;

    /// If this virtual memory is just a plain `GuestMemory` object underneath without an IOMMU
    /// translation layer in between, return that `GuestMemory` object.
    fn physical_memory(&self) -> Option<&Self::PhysicalMemory> {
        None
    }
}

impl<M: GuestMemory> IoMemory for M {
    type PhysicalMemory = M;
    type Bitmap = <M::R as GuestMemoryRegion>::B;

    fn range_accessible(&self, addr: GuestAddress, count: usize, _access: Permissions) -> bool {
        if count <= 1 {
            <M as GuestMemory>::address_in_range(self, addr)
        } else if let Some(end) = addr.0.checked_add(count as u64 - 1) {
            <M as GuestMemory>::address_in_range(self, addr)
                && <M as GuestMemory>::address_in_range(self, GuestAddress(end))
        } else {
            false
        }
    }

    fn try_access<'a, F>(
        &'a self,
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
            &'a <Self::PhysicalMemory as GuestMemory>::R,
        ) -> Result<usize>,
    {
        <M as GuestMemory>::try_access(self, count, addr, f)
    }

    fn get_slice(
        &self,
        addr: GuestAddress,
        count: usize,
        _access: Permissions,
    ) -> Result<VolatileSlice<bitmap::MS<M>>> {
        <M as GuestMemory>::get_slice(self, addr, count)
    }

    fn physical_memory(&self) -> Option<&Self::PhysicalMemory> {
        Some(self)
    }
}
