// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Traits to track and access the physical memory of the guest.
//!
//! To make the abstraction as generic as possible, all the core traits declared here only define
//! methods to access guest's memory, and never define methods to manage (create, delete, insert,
//! remove etc) guest's memory. This way, the guest memory consumers (virtio device drivers,
//! vhost drivers and boot loaders etc) may be decoupled from the guest memory provider (typically
//! a hypervisor).
//!
//! Traits and Structs
//! - [`GuestAddress`](struct.GuestAddress.html): represents a guest physical address (GPA).
//! - [`MemoryRegionAddress`](struct.MemoryRegionAddress.html): represents an offset inside a
//!   region.
//! - [`GuestMemoryRegion`](trait.GuestMemoryRegion.html): represent a continuous region of guest's
//!   physical memory.
//! - [`GuestMemory`](trait.GuestMemory.html): represent a collection of `GuestMemoryRegion`
//!   objects.
//!   The main responsibilities of the `GuestMemory` trait are:
//!     - hide the detail of accessing guest's physical address.
//!     - map a request address to a `GuestMemoryRegion` object and relay the request to it.
//!     - handle cases where an access request spanning two or more `GuestMemoryRegion` objects.
//!
//! Whenever a collection of `GuestMemoryRegion` objects is mutable,
//! [`GuestAddressSpace`](trait.GuestAddressSpace.html) should be implemented
//! for clients to obtain a [`GuestMemory`] reference or smart pointer.
//!
//! The `GuestMemoryRegion` trait has an associated `B: Bitmap` type which is used to handle
//! dirty bitmap tracking. Backends are free to define the granularity (or whether tracking is
//! actually performed at all). Those that do implement tracking functionality are expected to
//! ensure the correctness of the underlying `Bytes` implementation. The user has to explicitly
//! record (using the handle returned by `GuestRegionMmap::bitmap`) write accesses performed
//! via pointers, references, or slices returned by methods of `GuestMemory`,`GuestMemoryRegion`,
//! `VolatileSlice`, `VolatileRef`, or `VolatileArrayRef`.

use std::ops::Deref;
use vm_memory_new::guest_memory::GuestAddressSpace as NewGuestAddressSpace;
pub use vm_memory_new::guest_memory::{
    Error, FileOffset, GuestAddress, GuestMemoryBackend as GuestMemory,
    GuestMemoryBackendSliceIterator as GuestMemorySliceIterator, GuestUsize, MemoryRegionAddress,
    Result,
};

/// `GuestAddressSpace` provides a way to retrieve a `GuestMemory` object.
/// The vm-memory crate already provides trivial implementation for
/// references to `GuestMemory` or reference-counted `GuestMemory` objects,
/// but the trait can also be implemented by any other struct in order
/// to provide temporary access to a snapshot of the memory map.
///
/// In order to support generic mutable memory maps, devices (or other things
/// that access memory) should store the memory as a `GuestAddressSpace<M>`.
/// This example shows that references can also be used as the `GuestAddressSpace`
/// implementation, providing a zero-cost abstraction whenever immutable memory
/// maps are sufficient.
///
/// # Examples (uses the `backend-mmap` and `backend-atomic` features)
///
/// ```
/// # #[cfg(feature = "backend-mmap")]
/// # {
/// # use std::sync::Arc;
/// # use vm_memory::{GuestAddress, GuestAddressSpace, GuestMemory, GuestMemoryMmap};
/// #
/// pub struct VirtioDevice<AS: GuestAddressSpace> {
///     mem: Option<AS>,
/// }
///
/// impl<AS: GuestAddressSpace> VirtioDevice<AS> {
///     fn new() -> Self {
///         VirtioDevice { mem: None }
///     }
///     fn activate(&mut self, mem: AS) {
///         self.mem = Some(mem)
///     }
/// }
///
/// fn get_mmap() -> GuestMemoryMmap<()> {
///     let start_addr = GuestAddress(0x1000);
///     GuestMemoryMmap::from_ranges(&vec![(start_addr, 0x400)])
///         .expect("Could not create guest memory")
/// }
///
/// // Using `VirtioDevice` with an immutable GuestMemoryMmap:
/// let mut for_immutable_mmap = VirtioDevice::<&GuestMemoryMmap<()>>::new();
/// let mmap = get_mmap();
/// for_immutable_mmap.activate(&mmap);
/// let mut another = VirtioDevice::<&GuestMemoryMmap<()>>::new();
/// another.activate(&mmap);
///
/// # #[cfg(feature = "backend-atomic")]
/// # {
/// # use vm_memory::GuestMemoryAtomic;
/// // Using `VirtioDevice` with a mutable GuestMemoryMmap:
/// let mut for_mutable_mmap = VirtioDevice::<GuestMemoryAtomic<GuestMemoryMmap<()>>>::new();
/// let atomic = GuestMemoryAtomic::new(get_mmap());
/// for_mutable_mmap.activate(atomic.clone());
/// let mut another = VirtioDevice::<GuestMemoryAtomic<GuestMemoryMmap<()>>>::new();
/// another.activate(atomic.clone());
///
/// // atomic can be modified here...
/// # }
/// # }
/// ```
pub trait GuestAddressSpace: Clone {
    /// The type that will be used to access guest memory.
    type M: GuestMemory;

    /// A type that provides access to the memory.
    type T: Clone + Deref<Target = Self::M>;

    /// Return an object (e.g. a reference or guard) that can be used
    /// to access memory through this address space.  The object provides
    /// a consistent snapshot of the memory map.
    fn memory(&self) -> Self::T;
}

impl<M: NewGuestAddressSpace<M: GuestMemory>> GuestAddressSpace for M {
    type M = M::M;
    type T = M::T;

    fn memory(&self) -> Self::T {
        NewGuestAddressSpace::memory(self)
    }
}

#[cfg(all(test, feature = "backend-atomic", feature = "backend-mmap"))]
mod tests {
    use crate::{GuestAddress, GuestAddressSpace, GuestMemory, GuestMemoryAtomic, GuestMemoryMmap};
    use std::ops::Deref;

    /// Simple memory user encapsulating a `GuestAddressSpace` object.
    struct TestMemoryUser<M: GuestAddressSpace>(M);

    impl<M: GuestAddressSpace> TestMemoryUser<M> {
        fn new(memory: M) -> Self {
            TestMemoryUser(memory)
        }

        /// Assert that `self.0` has exactly `reference` memory regions.
        ///
        /// This verifies that `GuestAddressSpace::memory()` returns something we can actually use,
        /// i.e. that its memory type implements the `GuestMemory` trait as exported in 0.17, and
        /// not the `GuestMemory` trait from 0.18, which is not available in 0.17 and is thus
        /// unusable.
        ///
        /// (`.num_regions()` is just a simple way to verify the `GuestMemory` trait.)
        fn check_region_count(&self, reference: usize) {
            /// This inner function makes the trait requirement (`GuestMemory`) explicit.
            fn do_check_region_count(mem: impl Deref<Target: GuestMemory>, reference: usize) {
                assert_eq!(mem.num_regions(), reference);
            }

            do_check_region_count(self.0.memory(), reference);
        }
    }

    /// Verify that `GuestAddressSpace::memory()` returns a usable type, i.e one whose
    /// `Deref::Target` implements the `GuestMemory` trait that is actually exported in 0.17.
    #[test]
    fn test_guest_address_space_memory_access() {
        let mem = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x1000)]).unwrap();
        let user = TestMemoryUser::new(GuestMemoryAtomic::new(mem));
        user.check_region_count(1);
    }
}
