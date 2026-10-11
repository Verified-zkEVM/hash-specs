//! Throughput of the Lean fast specifications next to the implementations they are
//! differentially tested against.
//!
//! This is a record of relative efficiency, not a requirement: nothing fails if the Lean code
//! is slower. Run with `cargo bench`, then `python3 ../scripts/bench_report.py` to update
//! `BENCHMARKS.md`.

use aws_lc_rs::digest;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use sha2::Digest;
use std::time::Duration;

const SIZES: [usize; 4] = [64, 1024, 64 * 1024, 1024 * 1024];

fn bench_hash(c: &mut Criterion, name: &str, impls: &[(&str, &dyn Fn(&[u8]) -> Vec<u8>)]) {
    let mut group = c.benchmark_group(name);
    group.measurement_time(Duration::from_secs(3)).warm_up_time(Duration::from_millis(500));
    for &size in &SIZES {
        let m: Vec<u8> = (0..size).map(|i| i as u8).collect();
        group.throughput(Throughput::Bytes(size as u64));
        for (imp, f) in impls {
            group.bench_with_input(BenchmarkId::new(*imp, size), &m, |b, m| b.iter(|| f(m)));
        }
    }
    group.finish();
}

fn sha2(c: &mut Criterion) {
    bench_hash(c, "SHA-256", &[
        ("lean", &|m| hash_lean::sha256(m)),
        ("rustcrypto", &|m| sha2::Sha256::digest(m).to_vec()),
        ("aws-lc", &|m| digest::digest(&digest::SHA256, m).as_ref().to_vec()),
    ]);
    bench_hash(c, "SHA-512", &[
        ("lean", &|m| hash_lean::sha512(m)),
        ("rustcrypto", &|m| sha2::Sha512::digest(m).to_vec()),
        ("aws-lc", &|m| digest::digest(&digest::SHA512, m).as_ref().to_vec()),
    ]);
}

criterion_group!(benches, sha2);
criterion_main!(benches);
