// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Traits for allocating, handling and interacting with the VM's physical memory.
//!
//! For a typical hypervisor, there are several components, such as boot loader, virtual device
//! drivers, virtio backend drivers and vhost drivers etc, that need to access VM's physical memory.
//! This crate aims to provide a set of stable traits to decouple VM memory consumers from VM
//! memory providers. Based on these traits, VM memory consumers could access VM's physical memory
//! without knowing the implementation details of the VM memory provider. Thus hypervisor
//! components, such as boot loader, virtual device drivers, virtio backend drivers and vhost
//! drivers etc, could be shared and reused by multiple hypervisors.

#![deny(clippy::doc_markdown)]
#![deny(missing_docs)]

mod access;

#[macro_use]
pub mod address;
pub use address::{Address, AddressValue};

pub mod align;
pub use align::Aligned;

#[cfg(feature = "backend-atomic")]
pub mod atomic;
#[cfg(feature = "backend-atomic")]
pub use atomic::{GuestMemoryAtomic, GuestMemoryLoadGuard};

pub mod bytes;
pub use bytes::{ByteValued, Bytes};

pub mod endian;
pub use endian::{Be16, Be32, Be64, BeSize, Le16, Le32, Le64, LeSize};

pub mod guest_memory;
pub use guest_memory::{
    AlignedGuestAddress, AlignedMemoryRegionAddress, Error as GuestMemoryError, FileOffset,
    GuestAddress, GuestAddressSpace, GuestMemory, GuestMemoryRegion, GuestUsize,
    MemoryRegionAddress, Result as GuestMemoryResult,
};

#[cfg(all(feature = "backend-mmap", unix))]
mod mmap_unix;

#[cfg(all(feature = "backend-mmap", windows))]
mod mmap_windows;

#[cfg(feature = "backend-mmap")]
pub mod mmap;
#[cfg(feature = "backend-mmap")]
pub use mmap::{Error, GuestMemoryMmap, GuestRegionMmap, MmapRegion};

pub mod refs;
pub use refs::{ArrayRef, Ref};

pub mod volatile_memory;
pub use volatile_memory::{
    AtomicValued, Error as VolatileMemoryError, Result as VolatileMemoryResult, VolatileArrayRef,
    VolatileMemory, VolatileRef, VolatileSlice,
};

// Previous attempts showed it's not really obvious which is the fastest (best?) approach to
// bulk byte copies. This method is meant to be called whenever a copy is necessary,  so we can
// easily change the behaviour in the future by altering its actual implementation. For now, we
// simply rely on `std::ptr::copy_nonoverlapping`, which should be equivalent to `memcpy`.
unsafe fn copy_bytes(src: *const u8, dst: *mut u8, len: usize) {
    std::ptr::copy_nonoverlapping(src, dst, len)
}
