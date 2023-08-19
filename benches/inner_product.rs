//! Benchmarks for the inner product proof

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use itertools::Itertools;
use merlin::HashChainTranscript;
use mpc_bulletproof::InnerProductProof;
use mpc_stark::{
    algebra::{scalar::Scalar, stark_curve::StarkPoint},
    random_point,
};
use rand::thread_rng;

/// The max number of constraints to benchmark
const MAX_CONSTRAINTS_LN: usize = 16; // 2^10 = 1024

// -----------
// | Helpers |
// -----------

/// Generate a set of random scalars
fn random_scalars(n: usize) -> Vec<Scalar> {
    (0..n)
        .map(|_| Scalar::random(&mut thread_rng()))
        .collect_vec()
}

/// Generate a set of random points
fn random_points(n: usize) -> Vec<StarkPoint> {
    (0..n).map(|_| random_point()).collect_vec()
}

/// Benchmark a prover with a given number of constraints
#[allow(non_snake_case)]
fn bench_prover_with_size(n_elems: usize, c: &mut Criterion) {
    assert!(n_elems.is_power_of_two());

    let mut group = c.benchmark_group("inner_product");
    let benchmark_id = BenchmarkId::new("ipp-prover", n_elems);
    group.bench_function(benchmark_id, |b| {
        // Create the IPP inputs
        let mut transcript = HashChainTranscript::new(b"test");
        let Q = random_point();
        let G_factors = random_scalars(n_elems);
        let H_factors = random_scalars(n_elems);
        let G_vec = random_points(n_elems);
        let H_vec = random_points(n_elems);
        let a_vec = random_scalars(n_elems);
        let b_vec = random_scalars(n_elems);

        b.iter(|| {
            let _proof = InnerProductProof::create(
                &mut transcript,
                &Q,
                &G_factors,
                &H_factors,
                G_vec.clone(),
                H_vec.clone(),
                a_vec.clone(),
                b_vec.clone(),
            );
            black_box(_proof);
        })
    });
}

// --------------
// | Benchmarks |
// --------------

/// Benchmark the prover with a range of constraint sizes
fn bench_prover(c: &mut Criterion) {
    // Benchmark a range of constraint sizes
    for i in (1..=MAX_CONSTRAINTS_LN).map(|i| 1 << i) {
        bench_prover_with_size(i, c);
    }
}

criterion_group!(
    name = inner_product;
    config = Criterion::default().sample_size(10);
    targets = bench_prover,
);
criterion_main!(inner_product);
