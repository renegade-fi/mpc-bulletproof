//! Benchmarks for r1cs

use std::time::{Duration, Instant};

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use merlin::HashChainTranscript;
use mpc_bulletproof::{
    r1cs::{ConstraintSystem, Prover, R1CSProof, Verifier},
    BulletproofGens, PedersenGens,
};
use mpc_stark::{algebra::scalar::Scalar, random_point};
use rand::thread_rng;

/// The max number of constraints to benchmark
const MAX_CONSTRAINTS_LN: usize = 10; // 2^10 = 1024

// -----------
// | Helpers |
// -----------

/// Benchmark a prover with a given number of constraints
fn bench_prover_with_size(n_constraints: usize, c: &mut Criterion) {
    assert!(n_constraints.is_power_of_two());

    let mut group = c.benchmark_group("r1cs");
    let benchmark_id = BenchmarkId::new("prover", n_constraints);
    group.bench_function(benchmark_id, |b| {
        b.iter_custom(|n_iters| {
            // `Prover::prove` takes ownership of the constraint system, so we need custom
            // setup code and timing per-loop to only time the proof generation latency
            let mut total_time = Duration::ZERO;

            for _ in 0..n_iters {
                let (_proof, duration) = prove_sized_statement_with_timer(n_constraints);
                total_time += duration;
            }

            total_time
        });
    });
}

/// Benchmark a verifier with a given number of constraints
fn bench_verifier_with_size(n_constraints: usize, c: &mut Criterion) {
    assert!(n_constraints.is_power_of_two());

    let mut group = c.benchmark_group("r1cs");
    let benchmark_id = BenchmarkId::new("verifier", n_constraints);
    group.bench_function(benchmark_id, |b| {
        // Prove a statement
        let (proof, _duration) = prove_sized_statement_with_timer(n_constraints);

        b.iter_custom(|n_iters| {
            let mut total_time = Duration::ZERO;

            for _ in 0..n_iters {
                // Setup the verifier
                let pc_gens = PedersenGens::default();
                let mut transcript = HashChainTranscript::new(b"test");
                let mut verifier = Verifier::new(&pc_gens, &mut transcript);

                let bp_gens = BulletproofGens::new(n_constraints, 1 /* party_capacity */);

                // Apply the constraints
                let mut var = verifier.commit(random_point());
                for _ in 0..n_constraints {
                    let (_, _, new_var) = verifier.multiply(var.into(), var.into());
                    var = new_var;
                }

                // Verify the proof
                let start_time = Instant::now();
                assert!(black_box(verifier.verify(&proof, &bp_gens)).is_err());
                total_time += start_time.elapsed();
            }

            total_time
        });
    });
}

/// Prove a sized circuit and time *only* the prover latency
fn prove_sized_statement_with_timer(n_constraints: usize) -> (R1CSProof, Duration) {
    // Build a prover
    let pc_gens = PedersenGens::default();
    let mut transcript = HashChainTranscript::new(b"test");
    let mut prover = Prover::new(&pc_gens, &mut transcript);

    let bp_gens = BulletproofGens::new(n_constraints, 1 /* party_capacity */);

    // Allocate `n_constraints` constraints
    let mut rng = thread_rng();
    let val = Scalar::random(&mut rng);
    let (_, mut var) = prover.commit(val, Scalar::random(&mut rng));

    for _ in 0..n_constraints {
        (_, _, var) = prover.multiply(var.into(), var.into());
    }

    // Only time proof generation
    let start_time = Instant::now();
    let proof = prover.prove(&bp_gens).unwrap();
    (proof, start_time.elapsed())
}

// --------------
// | Benchmarks |
// --------------

/// Benchmark the prover's latency
fn bench_prover(c: &mut Criterion) {
    for i in (1..=MAX_CONSTRAINTS_LN).map(|i| 1usize << i) {
        bench_prover_with_size(i, c);
    }
}

/// Benchmarks the verifier's latency
fn bench_verifier(c: &mut Criterion) {
    for i in (1..=MAX_CONSTRAINTS_LN).map(|i| 1usize << i) {
        bench_verifier_with_size(i, c);
    }
}

criterion_group!(
    name = r1cs;
    config = Criterion::default().sample_size(10);
    targets = bench_prover, bench_verifier
);
criterion_main!(r1cs);
