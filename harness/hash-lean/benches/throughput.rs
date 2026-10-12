//! Throughput of the Lean fast specifications next to the implementations they are
//! differentially tested against.
//!
//! This is a record of relative efficiency, not a requirement: nothing fails if the Lean code
//! is slower. Run with `cargo bench`, then `python3 ../scripts/bench_report.py` to update
//! `BENCHMARKS.md`.

use aws_lc_rs::digest;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use sha2::Digest;
use tiny_keccak::Hasher;
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

fn keccak(c: &mut Criterion) {
    bench_hash(c, "SHA3-256", &[
        ("lean", &|m| hash_lean::sha3_256(m)),
        ("rustcrypto", &|m| sha3::Sha3_256::digest(m).to_vec()),
        ("aws-lc", &|m| digest::digest(&digest::SHA3_256, m).as_ref().to_vec()),
    ]);
    bench_hash(c, "Keccak-256", &[
        ("lean", &|m| hash_lean::keccak256(m)),
        ("rustcrypto", &|m| sha3::Keccak256::digest(m).to_vec()),
        ("tiny-keccak", &|m| {
            let mut k = tiny_keccak::Keccak::v256();
            k.update(m);
            let mut out = vec![0u8; 32];
            k.finalize(&mut out);
            out
        }),
    ]);
}

fn blake2(c: &mut Criterion) {
    use blake2::Digest as _;
    let b = hash_lean::Blake2Params { out_len: 64, key: &[], salt: &[], personal: &[] };
    let s = hash_lean::Blake2Params { out_len: 32, ..b };
    bench_hash(c, "BLAKE2b-512", &[
        ("lean", &|m| hash_lean::blake2b(&b, m)),
        ("blake2b_simd", &|m| blake2b_simd::blake2b(m).as_bytes().to_vec()),
        ("rustcrypto", &|m| blake2::Blake2b512::digest(m).to_vec()),
    ]);
    bench_hash(c, "BLAKE2s-256", &[
        ("lean", &|m| hash_lean::blake2s(&s, m)),
        ("blake2s_simd", &|m| blake2s_simd::blake2s(m).as_bytes().to_vec()),
        ("rustcrypto", &|m| blake2::Blake2s256::digest(m).to_vec()),
    ]);
}

criterion_group!(benches, sha2, keccak, blake2);
criterion_main!(benches);
