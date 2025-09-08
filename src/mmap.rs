// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! The default implementation for the [`GuestMemory`](trait.GuestMemory.html) trait.
//!
//! This implementation is mmap-ing the memory of the guest into the current process.

// re-export for backward compat, as the trait used to be defined in mmap.rs
pub use vm_memory_new::bitmap::NewBitmap;

#[cfg(all(not(feature = "xen"), target_family = "unix"))]
pub use vm_memory_new::mmap::MmapRegionBuilder;

#[cfg(all(feature = "xen", target_family = "unix"))]
pub use vm_memory_new::mmap::{MmapRange, MmapXenFlags};

pub use vm_memory_new::mmap::{
    FromRangesError, GuestMemoryMmap, GuestRegionMmap, MmapRegion, MmapRegionError,
};
