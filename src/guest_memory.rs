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

pub use vm_memory_new::guest_memory::{
    Error, FileOffset, GuestAddress, GuestAddressSpace, GuestMemoryBackend as GuestMemory,
    GuestMemoryBackendSliceIterator as GuestMemorySliceIterator, GuestUsize, MemoryRegionAddress,
    Result,
};
