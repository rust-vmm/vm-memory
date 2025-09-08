// Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Module containing versions of the standard library's [`Read`](std::io::Read) and
//! [`Write`](std::io::Write) traits compatible with volatile memory accesses.

pub use vm_memory_new::io::{ReadVolatile, WriteVolatile};
