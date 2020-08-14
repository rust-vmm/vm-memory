// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

extern crate criterion;

pub use criterion::{black_box, criterion_group, criterion_main, Criterion};

mod mmap;

#[cfg(feature = "backend-mmap")]
use mmap::benchmark_for_mmap;

pub fn criterion_benchmark(_c: &mut Criterion) {
    #[cfg(feature = "backend-mmap")]
    benchmark_for_mmap(_c);
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(200).measurement_time(std::time::Duration::from_secs(50));
    targets = criterion_benchmark
}

criterion_main! {
    benches,
}
