//! Groups integration tests for shared inner product proofs

use std::iter;

use bulletproofs::BulletproofGens;
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
use mpc_ristretto::{authenticated_scalar::AuthenticatedScalar, error::MpcError};
use rand_core::OsRng;
use sha3::Sha3_512;

use crate::{IntegrationTest, IntegrationTestArgs};

/// Tests that a simple inner product argument proves correctly
#[allow(non_snake_case)]
fn test_simple_inner_product(test_args: &IntegrationTestArgs) -> Result<(), String> {
    let n = 10;
    let mut rng = OsRng {};

    let bp_gens = BulletproofGens::new(n, 1);
    let G: Vec<RistrettoPoint> = bp_gens.share(0).G(n).cloned().collect();
    let H: Vec<RistrettoPoint> = bp_gens.share(0).H(n).cloned().collect();

    let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(n).collect();

    let y_inv = Scalar::random(&mut rng);
    let H_factor: Vec<Scalar> = bulletproofs::util::exp_iter(y_inv).take(n).collect();

    // Q would be determined upstream in the protocol, so we pick a random one.
    let Q = RistrettoPoint::hash_from_bytes::<Sha3_512>(b"test point");

    // Party 0 holds the first vector, party 1 holds the second
    // Expected inner product is 920
    let my_values = if test_args.party_id == 0 {
        vec![13, 42, 15]
    } else {
        vec![5, 0, 57]
    };
    let expected_inner_product = 920u64;

    let shared_a: Vec<AuthenticatedScalar<_, _>> = my_values
        .iter()
        .map(|value| {
            test_args
                .mpc_fabric
                .as_ref()
                .borrow()
                .allocate_private_u64(0 /* party_id */, *value)
        })
        .collect::<Result<Vec<_>, MpcError>>()
        .map_err(|err| format!("Error sharing a values: {:?}", err))?;

    let shared_b: Vec<AuthenticatedScalar<_, _>> = my_values
        .iter()
        .map(|value| {
            test_args
                .mpc_fabric
                .as_ref()
                .borrow()
                .allocate_private_u64(1 /* party_id */, *value)
        })
        .collect::<Result<Vec<_>, MpcError>>()
        .map_err(|err| format!("Error sharing b values: {:?}", err))?;

    Ok(())
}

inventory::submit!(IntegrationTest {
    name: "mpc-inner-product::test_simple_inner_product",
    test_fn: test_simple_inner_product,
});
