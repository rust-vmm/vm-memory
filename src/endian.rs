// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Explicit endian types useful for embedding in structs or reinterpreting data.
//!
//! Each endian type is guaarnteed to have the same size and alignment as a regular unsigned
//! primitive of the equal size.
//!
//! # Examples
//!
//! ```
//! # use vm_memory::{Be32, Le32};
//! #
//! let b: Be32 = From::from(3);
//! let l: Le32 = From::from(3);
//!
//! assert_eq!(b.to_native(), 3);
//! assert_eq!(l.to_native(), 3);
//! assert!(b == 3);
//! assert!(l == 3);
//!
//! let b_trans: u32 = unsafe { std::mem::transmute(b) };
//! let l_trans: u32 = unsafe { std::mem::transmute(l) };
//!
//! #[cfg(target_endian = "little")]
//! assert_eq!(l_trans, 3);
//! #[cfg(target_endian = "big")]
//! assert_eq!(b_trans, 3);
//!
//! assert_ne!(b_trans, l_trans);
//! ```

pub use vm_memory_new::endian::{Be16, Be32, Be64, BeSize, Le16, Le32, Le64, LeSize};
