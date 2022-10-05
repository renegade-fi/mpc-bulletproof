//! Groups integration tests for shared inner product proofs

use std::iter;

use bulletproofs::{r1cs_mpc::mpc_inner_product::SharedInnerProductProof, util, BulletproofGens};
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
use merlin::Transcript;
use mpc_ristretto::{
    authenticated_ristretto::AuthenticatedRistretto, authenticated_scalar::AuthenticatedScalar,
    error::MpcError,
};
use rand_core::OsRng;
use sha3::Sha3_512;

use crate::{IntegrationTest, IntegrationTestArgs, SharedMpcFabric};

/**
 * Utils
 */

/// Generates a random challenge scalar originating from the given party, and shares
/// it with the peer
fn generate_challenge_scalar(party_id: u64, fabric: SharedMpcFabric) -> Result<Scalar, String> {
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

/**
 * Tests
 */

/// Tests that a simple inner product argument proves correctly
#[allow(non_snake_case)]
fn test_simple_inner_product(test_args: &IntegrationTestArgs) -> Result<(), String> {
    let n = 2;
    let borrowed_fabric = test_args.mpc_fabric.as_ref().borrow();

    let bp_gens = BulletproofGens::new(n, 1);
    let G: Vec<AuthenticatedRistretto<_, _>> = bp_gens
        .share(0)
        .G(n)
        .cloned()
        .map(|value| borrowed_fabric.allocate_public_ristretto_point(value))
        .collect();
    let H: Vec<AuthenticatedRistretto<_, _>> = bp_gens
        .share(0)
        .H(n)
        .cloned()
        .map(|value| borrowed_fabric.allocate_public_ristretto_point(value))
        .collect();

    let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(n).collect();

    let y_inv = generate_challenge_scalar(0 /* party_id */, test_args.mpc_fabric.clone())?;
    let H_factors: Vec<Scalar> = util::exp_iter(y_inv).take(n).collect();

    // Q would be determined upstream in the protocol, so we pick a random one.
    let Q = borrowed_fabric.allocate_public_ristretto_point(RistrettoPoint::hash_from_bytes::<
        Sha3_512,
    >(b"test point"));

    // Party 0 holds the first vector, party 1 holds the second
    // Expected inner product is 920
    let my_values = if test_args.party_id == 0 {
        vec![13, 42]
    } else {
        vec![5, 0]
    };
    let expected_inner_product = 65u64;

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

    let b_prime = shared_b
        .iter()
        .zip(util::exp_iter(y_inv))
        .map(|(bi, yi)| bi * yi);

    let P = AuthenticatedRistretto::multiscalar_mul(
        shared_a.iter().cloned().chain(b_prime).chain(iter::once(c)),
        G.iter().chain(H.iter()).chain(iter::once(&Q)),
    );

    let mut transcript = Transcript::new(b"test_simple_inner_product");
    let proof = SharedInnerProductProof::create(
        &mut transcript,
        &Q,
        &G_factors,
        &H_factors,
        G.clone(),
        H.clone(),
        shared_a,
        shared_b,
        test_args.mpc_fabric.clone(),
    )
    .map_err(|err| format!("Error proving: {:?}", err))?;

    // Open the proof and verify it
    let opened_proof = proof
        .open()
        .map_err(|err| format!("Error opening proof: {:?}", err))?;

    let P_open = P
        .open()
        .map_err(|err| format!("Error opening P: {:?}", err))?;

    let mut verifier_transcript = Transcript::new(b"test_simple_inner_product");
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

inventory::submit!(IntegrationTest {
    name: "mpc-inner-product::test_simple_inner_product",
    test_fn: test_simple_inner_product,
});
