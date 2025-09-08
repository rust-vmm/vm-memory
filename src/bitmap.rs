// Copyright 2021 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! This module holds abstractions that enable tracking the areas dirtied by writes of a specified
//! length to a given offset. In particular, this is used to track write accesses within a
//! `GuestMemoryRegion` object, and the resulting bitmaps can then be aggregated to build the
//! global view for an entire `GuestMemory` object.

#[cfg(feature = "backend-bitmap")]
pub use vm_memory_new::bitmap::{ArcSlice, AtomicBitmap, RefSlice};

pub use vm_memory_new::bitmap::{Bitmap, BitmapSlice, NewBitmap, WithBitmapSlice, BS, MS};
