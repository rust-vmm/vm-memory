// Portions Copyright 2019 Red Hat, Inc.
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Define the `ByteValued` trait to mark that it is safe to instantiate the struct with random
//! data.

pub use vm_memory_new::bytes::{AtomicAccess, ByteValued, Bytes};
