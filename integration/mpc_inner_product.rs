//! Groups integration tests for shared inner product proofs

use std::iter;

use futures::future::join_all;
use itertools::Itertools;
use merlin::Transcript;
use mpc_bulletproof::{r1cs_mpc::SharedInnerProductProof, util, BulletproofGens, MpcTranscript};
use mpc_stark::{
    algebra::{
        authenticated_scalar::AuthenticatedScalarResult,
        authenticated_stark_point::AuthenticatedStarkPointResult,
        scalar::{Scalar, ScalarResult},
        stark_curve::StarkPoint,
    },
    fabric::MpcFabric,
    random_point, PARTY0, PARTY1,
};
use rand::{rngs::OsRng, thread_rng, Rng, RngCore};
use tokio::runtime::Handle;

use crate::{IntegrationTest, IntegrationTestArgs};

// -------------
// | Constants |
// -------------

/// The seed of the test transcripts
pub(crate) const TRANSCRIPT_SEED: &str = "test_inner_product";

// ---------
// | Utils |
// ---------

/// Generates a random challenge scalar originating from the given party, and shares
/// it with the peer
fn generate_challenge_scalar(fabric: MpcFabric) -> ScalarResult {
    let mut rng = OsRng {};
    let random_scalar = Scalar::random(&mut rng);

    fabric.allocate_scalar(random_scalar)
}

#[allow(non_snake_case)]
fn create_input_commitment(
    a: &[AuthenticatedScalarResult],
    b: &[AuthenticatedScalarResult],
    c: &ScalarResult,
    y_inv: ScalarResult,
    fabric: MpcFabric,
) -> AuthenticatedStarkPointResult {
    assert_eq!(a.len(), b.len());
    let n = a.len();
    assert!(n.is_power_of_two());

    // Build generators for the commitment
    let bp_gens = BulletproofGens::new(n, 1);
    let G: Vec<StarkPoint> = bp_gens.share(0).G(n).copied().collect_vec();
    let H: Vec<StarkPoint> = bp_gens.share(0).H(n).copied().collect_vec();

    // Q is the generator used for `c`
    let Q = random_point();

    // Pre-multiply b by iterated powers of y_inv
    let y_inv_powers = util::exp_iter_result(y_inv, b.len(), &fabric);
    let b_prime = b.iter().zip(y_inv_powers.iter()).map(|(bi, yi)| bi * yi);

    StarkPoint::msm_authenticated_iter(
        a.iter().cloned().chain(b_prime),
        G.iter().chain(H.iter()).copied(),
    ) + c * Q
}

#[allow(non_snake_case)]
fn prove(
    a: &[AuthenticatedScalarResult],
    b: &[AuthenticatedScalarResult],
    y_inv: ScalarResult,
    fabric: MpcFabric,
) -> Result<SharedInnerProductProof, String> {
    assert_eq!(a.len(), b.len());
    let n = a.len();
    assert!(n.is_power_of_two());

    // Create the generators for the proof
    let bp_gens = BulletproofGens::new(n, 1);
    let G: Vec<StarkPoint> = bp_gens.share(0).G(n).cloned().collect_vec();
    let H: Vec<StarkPoint> = bp_gens.share(0).H(n).cloned().collect_vec();

    // Create multipliers for the generators
    let G_factors: Vec<ScalarResult> = iter::repeat(Scalar::one())
        .take(n)
        .map(|x| fabric.allocate_scalar(x))
        .collect();
    let H_factors: Vec<ScalarResult> = util::exp_iter_result(y_inv, n, &fabric);

    // Q is the generator used to commit to the inner product result `c`
    let Q = fabric.allocate_point(random_point());

    // Generate the inner product proof
    let transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
    let mut mpc_transcript = MpcTranscript::new(transcript, fabric.clone());
    SharedInnerProductProof::create(
        &mut mpc_transcript,
        Q,
        &G_factors,
        &H_factors,
        G,
        H,
        a.to_vec(),
        b.to_vec(),
        &fabric,
    )
    .map_err(|err| format!("Error proving: {:?}", err))
}

#[allow(non_snake_case)]
fn prove_and_verify(
    a: &[AuthenticatedScalarResult],
    b: &[AuthenticatedScalarResult],
    c: &ScalarResult,
    y_inv: ScalarResult,
    fabric: MpcFabric,
) -> Result<(), String> {
    assert_eq!(a.len(), b.len());
    let n = a.len();
    assert!(n.is_power_of_two());

    // Create a commitment to the input
    let P = create_input_commitment(a, b, c, y_inv.clone(), fabric.clone());

    // Create the generators for the proof
    let bp_gens = BulletproofGens::new(n, 1);
    let G: Vec<StarkPoint> = bp_gens.share(0).G(n).cloned().collect_vec();
    let H: Vec<StarkPoint> = bp_gens.share(0).H(n).cloned().collect_vec();

    // Create multipliers for the generators
    let G_factors: Vec<ScalarResult> = iter::repeat(Scalar::one())
        .take(n)
        .map(|x| fabric.allocate_scalar(x))
        .collect();
    let H_factors: Vec<ScalarResult> = util::exp_iter_result(y_inv, n, &fabric);

    // Q is the generator used to commit to the inner product result `c`
    let Q = fabric.allocate_point(random_point());

    // Generate the inner product proof
    let transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
    let mut mpc_transcript = MpcTranscript::new(transcript, fabric.clone());
    let proof = SharedInnerProductProof::create(
        &mut mpc_transcript,
        Q.clone(),
        &G_factors,
        &H_factors,
        G.clone(),
        H.clone(),
        a.to_vec(),
        b.to_vec(),
        &fabric,
    )
    .map_err(|err| format!("Error proving: {:?}", err))?;

    println!("\ncreated proof");

    // Open the proof and the input commitment, then verify them
    let opened_proof = proof
        .open()
        .map_err(|err| format!("Error opening proof: {:?}", err))?;

    println!("opened proof");

    let P_open = Handle::current().block_on(P.open());
    let Q = Handle::current().block_on(Q);
    let G_factors = Handle::current().block_on(join_all(G_factors.into_iter()));
    let H_factors = Handle::current().block_on(join_all(H_factors.into_iter()));
    let mut verifier_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
    if opened_proof
        .verify(
            n,
            &mut verifier_transcript,
            G_factors,
            H_factors,
            &P_open,
            &Q,
            &G,
            &H,
        )
        .is_err()
    {
        return Err("proof verification failed...".to_string());
    }

    println!("verified proof");

    Ok(())
}

// ---------
// | Tests |
// ---------

/// Tests that a simple inner product argument proves correctly
fn test_simple_inner_product(test_args: &IntegrationTestArgs) -> Result<(), String> {
    // Party 0 holds the first vector, party 1 holds the second
    // Expected inner product is 920
    let my_values = if test_args.party_id == 0 {
        vec![13, 42]
    } else {
        vec![5, 0]
    };
    let expected_inner_product = 65u64;

    // Share the values with the peer
    let fabric = &test_args.mpc_fabric;
    let shared_a: Vec<AuthenticatedScalarResult> = my_values
        .iter()
        .map(|value| fabric.share_scalar(*value, PARTY0))
        .collect_vec();

    let shared_b: Vec<AuthenticatedScalarResult> = my_values
        .iter()
        .map(|value| fabric.share_scalar(*value, PARTY1))
        .collect_vec();
    let c: ScalarResult = fabric.allocate_scalar(expected_inner_product);

    let y_inv = generate_challenge_scalar(fabric.clone());

    prove_and_verify(
        &shared_a,
        &shared_b,
        &c,
        y_inv,
        test_args.mpc_fabric.clone(),
    )
}

// Tests an inner product in which the values of party1 and party0 are interleaved
fn test_interleaved_inner_product(test_args: &IntegrationTestArgs) -> Result<(), String> {
    // Party 0 holds (a1, a2, a3) and party 1 holds (b1, b2, b3)
    // We prove the inner product a1 * a2 + a3 * b1 + b2 * b3
    let my_values = if test_args.party_id == 0 {
        vec![2u64, 3u64, 4u64, 0u64]
    } else {
        vec![5u64, 6u64, 7u64, 0u64]
    };

    // Share the values with the peer
    let fabric = &test_args.mpc_fabric;
    let party0_values: Vec<AuthenticatedScalarResult> = my_values
        .iter()
        .map(|value| fabric.share_scalar(*value, PARTY0))
        .collect_vec();
    let party1_values: Vec<AuthenticatedScalarResult> = my_values
        .iter()
        .map(|value| fabric.share_scalar(*value, PARTY1))
        .collect_vec();

    let a = vec![
        party0_values[0].clone(),
        party0_values[2].clone(),
        party1_values[1].clone(),
        // Pad to a power of 2
        party0_values[3].clone(),
    ];
    let b = vec![
        party0_values[1].clone(),
        party1_values[0].clone(),
        party1_values[2].clone(),
        // Pad to a power of 2
        party1_values[3].clone(),
    ];

    // 2 * 3 + 4 * 5 + 6 * 7 = 68
    let c = fabric.allocate_scalar(68);
    let y_inv = generate_challenge_scalar(test_args.mpc_fabric.clone());

    prove_and_verify(&a, &b, &c, y_inv, test_args.mpc_fabric.clone())
}

/// Tests a larger inner product of random values
///
/// The two parties perform a size n inner product, where each index of a and b
/// are assigned randomly to party 0 or party 1. These parties then choose random
/// values for the inner product
fn test_random_inner_product(test_args: &IntegrationTestArgs) -> Result<(), String> {
    // Setup
    let n = 32;
    let fabric = &test_args.mpc_fabric;

    // Party 0 randomly assigns indices
    let mut rng = thread_rng();
    let index_assignment = (0..2 * n)
        .map(|_| rng.gen_range(0..2))
        .map(|value| {
            if fabric.party_id() == PARTY0 {
                fabric.send_value(fabric.allocate_scalar(value))
            } else {
                fabric.receive_value()
            }
        })
        .collect_vec();
    let mut assignments = Handle::current().block_on(join_all(index_assignment.into_iter()));

    // Count the number of elements the local party is to allocate
    let n_party0 = assignments
        .iter()
        .copied()
        .filter(|value| *value == Scalar::from(0u64))
        .count();
    let n_party1 = 2 * n - n_party0;

    // Party 0 generates their vector of random values and shares it
    let mut party0_values = (0..n_party0)
        .map(|_| fabric.share_scalar(rng.next_u64(), PARTY0))
        .collect_vec();

    let mut party1_values = (0..n_party1)
        .map(|_| fabric.share_scalar(rng.next_u64(), PARTY1))
        .collect_vec();

    // From the shared values of each party, construct `a` and `b`
    let all_values = (0..2 * n)
        .map(|_| {
            if assignments.remove(0) == Scalar::from(0u64) {
                party0_values.remove(0)
            } else {
                party1_values.remove(0)
            }
        })
        .collect::<Vec<AuthenticatedScalarResult>>();

    let a = &all_values[..n];
    let b = &all_values[n..];

    let expected_inner_product = a
        .iter()
        .zip(b.iter())
        .fold(fabric.zero_authenticated(), |acc, (ai, bi)| acc + ai * bi)
        .open();

    let y_inv = generate_challenge_scalar(test_args.mpc_fabric.clone());

    // Prove and verify the inner product
    prove_and_verify(
        a,
        b,
        &expected_inner_product,
        y_inv,
        test_args.mpc_fabric.clone(),
    )
}

/// Tests that opening a modified proof fails authentication
fn test_malleable_proof(test_args: &IntegrationTestArgs) -> Result<(), String> {
    let fabric = &test_args.mpc_fabric;

    // Party 0 holds the first vector, party 1 holds the second
    // Expected inner product is 920
    let my_values = if test_args.party_id == 0 {
        vec![13, 42]
    } else {
        vec![5, 0]
    };

    // Share the values with the peer
    let shared_a = my_values
        .iter()
        .map(|value| fabric.share_scalar(*value, PARTY0))
        .collect_vec();

    let shared_b = my_values
        .iter()
        .map(|value| fabric.share_scalar(*value, PARTY1))
        .collect_vec();
    let y_inv = generate_challenge_scalar(test_args.mpc_fabric.clone());

    // Create a proof
    let mut proof = prove(&shared_a, &shared_b, y_inv, test_args.mpc_fabric.clone())?;

    // Party 0 tries to modify the proof
    if test_args.party_id == 0 {
        proof.a = proof.a + Scalar::from(2u64);
    }

    // Open and ensure that authentication fails
    proof.open().map_or(Ok(()), |_| {
        Err("Expected authentication failure, authentication passed...")
    })?;

    Ok(())
}

// Take inventory
inventory::submit!(IntegrationTest {
    name: "mpc-inner-product::test_simple_inner_product",
    test_fn: test_simple_inner_product,
});

inventory::submit!(IntegrationTest {
    name: "mpc-inner-product::test_interleaved_inner_product",
    test_fn: test_interleaved_inner_product,
});

inventory::submit!(IntegrationTest {
    name: "mpc-inner-product::test_random_inner_product",
    test_fn: test_random_inner_product,
});

inventory::submit!(IntegrationTest {
    name: "mpc-inner-product::test_malleable_proof",
    test_fn: test_malleable_proof,
});
