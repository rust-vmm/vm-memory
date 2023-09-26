// Copyright 2021 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

mod atomic_bitmap;
mod atomic_bitmap_arc;
#[cfg(all(feature = "backend-bitmap-mmap", unix))]
mod atomic_bitmap_mmap;
mod slice;

pub use atomic_bitmap::AtomicBitmap;
pub use atomic_bitmap_arc::AtomicBitmapArc;
pub use slice::{ArcSlice, RefSlice};

#[cfg(all(feature = "backend-bitmap-mmap", unix))]
pub use atomic_bitmap_mmap::BitmapRegion;
