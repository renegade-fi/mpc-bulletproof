//! Groups integration tests for shared inner product proofs

use std::iter;

use bulletproofs::{r1cs_mpc::SharedInnerProductProof, util, BulletproofGens};
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
use merlin::Transcript;
use mpc_ristretto::{
    authenticated_ristretto::AuthenticatedRistretto,
    authenticated_scalar::AuthenticatedScalar,
    beaver::SharedValueSource,
    error::{MpcError, MpcNetworkError},
    network::MpcNetwork,
};
use rand::{thread_rng, Rng, RngCore};
use rand_core::OsRng;
use sha3::Sha3_512;

use crate::{IntegrationTest, IntegrationTestArgs, SharedMpcFabric};

/**
 * Constants
 */
pub(crate) const TEST_PHRASE: &str = "test point";
pub(crate) const TRANSCRIPT_SEED: &str = "test_inner_product";

/**
 * Utils
 */

/// Generates a random challenge scalar originating from the given party, and shares
/// it with the peer
fn generate_challenge_scalar<N, S>(
    party_id: u64,
    fabric: SharedMpcFabric<N, S>,
) -> Result<Scalar, String>
where
    N: MpcNetwork + Send,
    S: SharedValueSource<Scalar>,
{
    let mut rng = OsRng {};
    let random_scalar = Scalar::random(&mut rng);

    fabric
        .as_ref()
        .borrow()
        .allocate_private_scalar(party_id, random_scalar)
        .map_err(|err| format!("Error sharing random value: {:?}", err))?
        .open()
        .map_err(|err| format!("Error opening random value: {:?}", err))
        .map(|value| value.to_scalar())
}

#[allow(non_snake_case)]
fn create_input_commitment<N, S>(
    a: &[AuthenticatedScalar<N, S>],
    b: &[AuthenticatedScalar<N, S>],
    c: &AuthenticatedScalar<N, S>,
    y_inv: Scalar,
    fabric: SharedMpcFabric<N, S>,
) -> AuthenticatedRistretto<N, S>
where
    N: MpcNetwork + Send,
    S: SharedValueSource<Scalar>,
{
    assert_eq!(a.len(), b.len());
    let n = a.len();
    assert!(n.is_power_of_two());

    // Create a reusable borrow of the MPC fabric
    let borrowed_fabric = fabric.as_ref().borrow();

    // Build generators for the commitment
    let bp_gens = BulletproofGens::new(n, 1);
    let G: Vec<AuthenticatedRistretto<_, _>> = bp_gens
        .share(0)
        .G(n)
        .cloned()
        .map(|value| borrowed_fabric.allocate_public_ristretto(value))
        .collect();
    let H: Vec<AuthenticatedRistretto<_, _>> = bp_gens
        .share(0)
        .H(n)
        .cloned()
        .map(|value| borrowed_fabric.allocate_public_ristretto(value))
        .collect();

    // Q is the generator used for `c`
    let Q = borrowed_fabric.allocate_public_ristretto(RistrettoPoint::hash_from_bytes::<Sha3_512>(
        TEST_PHRASE.as_bytes(),
    ));

    // Pre-multiply b by iterated powers of y_inv
    let b_prime = b.iter().zip(util::exp_iter(y_inv)).map(|(bi, yi)| bi * yi);

    AuthenticatedRistretto::multiscalar_mul(
        a.iter()
            .cloned()
            .chain(b_prime)
            .chain(iter::once(c.clone())),
        G.iter().chain(H.iter()).chain(iter::once(&Q)),
    )
}

#[allow(non_snake_case)]
fn prove<N, S>(
    a: &[AuthenticatedScalar<N, S>],
    b: &[AuthenticatedScalar<N, S>],
    y_inv: Scalar,
    fabric: SharedMpcFabric<N, S>,
) -> Result<SharedInnerProductProof<N, S>, String>
where
    N: MpcNetwork + Send,
    S: SharedValueSource<Scalar>,
{
    assert_eq!(a.len(), b.len());
    let n = a.len();
    assert!(n.is_power_of_two());

    // Create a reusable borrow
    let borrowed_fabric = fabric.as_ref().borrow();

    // Create the generators for the proof
    let bp_gens = BulletproofGens::new(n, 1);
    let G: Vec<AuthenticatedRistretto<_, _>> = bp_gens
        .share(0)
        .G(n)
        .cloned()
        .map(|value| borrowed_fabric.allocate_public_ristretto(value))
        .collect();
    let H: Vec<AuthenticatedRistretto<_, _>> = bp_gens
        .share(0)
        .H(n)
        .cloned()
        .map(|value| borrowed_fabric.allocate_public_ristretto(value))
        .collect();

    // Create multipliers for the generators
    let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(n).collect();
    let H_factors: Vec<Scalar> = util::exp_iter(y_inv).take(n).collect();

    // Q is the generator used to commit to the inner product result `c`
    let Q = borrowed_fabric.allocate_public_ristretto(RistrettoPoint::hash_from_bytes::<Sha3_512>(
        TEST_PHRASE.as_bytes(),
    ));

    // Generate the inner product proof
    let mut transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
    SharedInnerProductProof::create(
        &mut transcript,
        &Q,
        &G_factors,
        &H_factors,
        G,
        H,
        a.to_vec(),
        b.to_vec(),
        fabric.clone(),
    )
    .map_err(|err| format!("Error proving: {:?}", err))
}

#[allow(non_snake_case)]
fn prove_and_verify<N, S>(
    a: &[AuthenticatedScalar<N, S>],
    b: &[AuthenticatedScalar<N, S>],
    c: &AuthenticatedScalar<N, S>,
    y_inv: Scalar,
    fabric: SharedMpcFabric<N, S>,
) -> Result<(), String>
where
    N: MpcNetwork + Send,
    S: SharedValueSource<Scalar>,
{
    assert_eq!(a.len(), b.len());
    let n = a.len();
    assert!(n.is_power_of_two());

    // Create a commitment to the input
    let P = create_input_commitment(a, b, c, y_inv, fabric.clone());

    // Create a reusable borrow
    let borrowed_fabric = fabric.as_ref().borrow();

    // Create the generators for the proof
    let bp_gens = BulletproofGens::new(n, 1);
    let G: Vec<AuthenticatedRistretto<_, _>> = bp_gens
        .share(0)
        .G(n)
        .cloned()
        .map(|value| borrowed_fabric.allocate_public_ristretto(value))
        .collect();
    let H: Vec<AuthenticatedRistretto<_, _>> = bp_gens
        .share(0)
        .H(n)
        .cloned()
        .map(|value| borrowed_fabric.allocate_public_ristretto(value))
        .collect();

    // Create multipliers for the generators
    let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(n).collect();
    let H_factors: Vec<Scalar> = util::exp_iter(y_inv).take(n).collect();

    // Q is the generator used to commit to the inner product result `c`
    let Q = borrowed_fabric.allocate_public_ristretto(RistrettoPoint::hash_from_bytes::<Sha3_512>(
        TEST_PHRASE.as_bytes(),
    ));

    // Generate the inner product proof
    let mut transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
    let proof = SharedInnerProductProof::create(
        &mut transcript,
        &Q,
        &G_factors,
        &H_factors,
        G.clone(),
        H.clone(),
        a.to_vec(),
        b.to_vec(),
        fabric.clone(),
    )
    .map_err(|err| format!("Error proving: {:?}", err))?;

    // Open the proof and the input commitment, then verify them
    let opened_proof = proof
        .open()
        .map_err(|err| format!("Error opening proof: {:?}", err))?;

    let P_open = P
        .open()
        .map_err(|err| format!("Error opening P: {:?}", err))?;

    let mut verifier_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
    if opened_proof
        .verify(
            n,
            &mut verifier_transcript,
            G_factors,
            H_factors,
            &P_open.to_ristretto(),
            &Q.to_ristretto(),
            &G.iter()
                .map(|value| value.to_ristretto())
                .collect::<Vec<_>>(),
            &H.iter()
                .map(|value| value.to_ristretto())
                .collect::<Vec<_>>(),
        )
        .is_err()
    {
        return Err("proof verification failed...".to_string());
    }

    Ok(())
}

/**
 * Tests
 */

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
    let borrowed_fabric = test_args.mpc_fabric.as_ref().borrow();
    let shared_a: Vec<AuthenticatedScalar<_, _>> = my_values
        .iter()
        .map(|value| {
            borrowed_fabric.allocate_private_u64(0 /* party_id */, *value)
        })
        .collect::<Result<Vec<_>, MpcError>>()
        .map_err(|err| format!("Error sharing a values: {:?}", err))?;

    let shared_b: Vec<AuthenticatedScalar<_, _>> = my_values
        .iter()
        .map(|value| {
            borrowed_fabric.allocate_private_u64(1 /* party_id */, *value)
        })
        .collect::<Result<Vec<_>, MpcError>>()
        .map_err(|err| format!("Error sharing b values: {:?}", err))?;
    let c: AuthenticatedScalar<_, _> = borrowed_fabric.allocate_public_u64(expected_inner_product);
    let y_inv = generate_challenge_scalar(0 /* party_id */, test_args.mpc_fabric.clone())?;

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
    let borrowed_fabric = test_args.mpc_fabric.as_ref().borrow();
    let party0_values: Vec<AuthenticatedScalar<_, _>> = my_values
        .iter()
        .map(|value| {
            borrowed_fabric.allocate_private_u64(0 /* party_id */, *value)
        })
        .collect::<Result<Vec<_>, MpcError>>()
        .map_err(|err| format!("Error sharing a values: {:?}", err))?;

    let party1_values: Vec<AuthenticatedScalar<_, _>> = my_values
        .iter()
        .map(|value| {
            borrowed_fabric.allocate_private_u64(1 /* party_id */, *value)
        })
        .collect::<Result<Vec<_>, MpcError>>()
        .map_err(|err| format!("Error sharing b values: {:?}", err))?;
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
    let c = borrowed_fabric.allocate_public_u64(68);
    let y_inv = generate_challenge_scalar(0 /* party_id */, test_args.mpc_fabric.clone())?;

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
    let borrowed_fabric = test_args.mpc_fabric.as_ref().borrow();

    // Party 0 randomly assigns indices
    let mut rng = thread_rng();
    let index_assignment: Vec<AuthenticatedScalar<_, _>> = (0..2 * n) // 2n values to fill a and b
        .map(|_| {
            borrowed_fabric.allocate_private_u64(0 /* party_id */, rng.gen_range(0, 2))
        }) // Random number in {0, 1}
        .collect::<Result<Vec<AuthenticatedScalar<_, _>>, MpcError>>()
        .map_err(|err| format!("Error sharing index assignment: {:?}", err))?;

    // Open the index assignment
    let mut shared_index_assignment = index_assignment
        .iter()
        .map(|index| index.open())
        .collect::<Result<Vec<AuthenticatedScalar<_, _>>, MpcNetworkError>>()
        .map_err(|err| format!("Error opening index assingment: {:?}", err))?;

    // Count the number of elements the local party is to allocate
    let n_party0 = shared_index_assignment
        .iter()
        .filter(|value| value.to_scalar().eq(&Scalar::from(0u64)))
        .count();
    let n_party1 = 2 * n - n_party0;

    // Party 0 generates their vector of random values and shares it
    let mut party0_values = (0..n_party0)
        .map(|_| {
            borrowed_fabric.allocate_private_u64(0 /* party_id */, rng.next_u64())
        })
        .collect::<Result<Vec<AuthenticatedScalar<_, _>>, MpcError>>()
        .map_err(|err| format!("Error sharing party 0 values: {:?}", err))?;

    let mut party1_values = (0..n_party1)
        .map(|_| {
            borrowed_fabric.allocate_private_u64(1 /* party_id */, rng.next_u64())
        })
        .collect::<Result<Vec<AuthenticatedScalar<_, _>>, MpcError>>()
        .map_err(|err| format!("ERror sharing party 1 values: {:?}", err))?;

    // From the shared values of each party, construct `a` and `b`
    let all_values = (0..2 * n)
        .map(|_| {
            if shared_index_assignment.pop().unwrap().to_scalar() == Scalar::from(0u64) {
                party0_values.remove(0)
            } else {
                party1_values.remove(0)
            }
        })
        .collect::<Vec<AuthenticatedScalar<_, _>>>();

    let a = &all_values[..n];
    let b = &all_values[n..];

    let expected_inner_product = a
        .iter()
        .zip(b.iter())
        .fold(
            borrowed_fabric.allocate_zeros(1)[0].clone(),
            |acc, (ai, bi)| acc + ai * bi,
        )
        .open()
        .map_err(|err| format!("Error opening value: {:?}", err))?;

    let y_inv = generate_challenge_scalar(0 /* party_id */, test_args.mpc_fabric.clone())
        .map_err(|err| format!("Error sharing value: {:?}", err))?;

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
    // Party 0 holds the first vector, party 1 holds the second
    // Expected inner product is 920
    let my_values = if test_args.party_id == 0 {
        vec![13, 42]
    } else {
        vec![5, 0]
    };

    // Share the values with the peer
    let borrowed_fabric = test_args.mpc_fabric.as_ref().borrow();
    let shared_a: Vec<AuthenticatedScalar<_, _>> = my_values
        .iter()
        .map(|value| {
            borrowed_fabric.allocate_private_u64(0 /* party_id */, *value)
        })
        .collect::<Result<Vec<_>, MpcError>>()
        .map_err(|err| format!("Error sharing a values: {:?}", err))?;

    let shared_b: Vec<AuthenticatedScalar<_, _>> = my_values
        .iter()
        .map(|value| {
            borrowed_fabric.allocate_private_u64(1 /* party_id */, *value)
        })
        .collect::<Result<Vec<_>, MpcError>>()
        .map_err(|err| format!("Error sharing b values: {:?}", err))?;
    let y_inv = generate_challenge_scalar(0 /* party_id */, test_args.mpc_fabric.clone())?;

    // Create a proof
    let mut proof = prove(&shared_a, &shared_b, y_inv, test_args.mpc_fabric.clone())?;

    // Party 0 tries to modify the proof
    if test_args.party_id == 0 {
        proof.a += Scalar::from(2u64);
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
