//! Groups tests for the synchronized MPC transcript

use itertools::Itertools;
use merlin::Transcript;
use mpc_bulletproof::MpcTranscript;
use mpc_stark::{algebra::scalar::Scalar, random_point, PARTY0, PARTY1};
use rand::thread_rng;

use crate::{
    helpers::{assert_scalars_eq, await_result},
    IntegrationTest, IntegrationTestArgs,
};

/// Tests adding many scalars to the transcript
fn test_add_scalars(test_args: &IntegrationTestArgs) -> Result<(), String> {
    let fabric = &test_args.mpc_fabric;

    let n = 10;
    let mut rng = thread_rng();
    let my_scalars = (0..n).map(|_| Scalar::random(&mut rng)).collect_vec();

    // Share the scalars
    let party0_scalars = my_scalars
        .iter()
        .map(|s| fabric.share_scalar(*s, PARTY0))
        .collect_vec();
    let party1_scalars = my_scalars
        .iter()
        .map(|s| fabric.share_scalar(*s, PARTY1))
        .collect_vec();

    // Open all scalars and append their results to the transcript
    let opened_scalars = party0_scalars
        .iter()
        .chain(party1_scalars.iter())
        .map(|s| s.open_authenticated())
        .map(|s| s.value)
        .collect_vec();

    let mut transcript = MpcTranscript::new(Transcript::new(b"test"), fabric.clone());
    for scalar in opened_scalars.into_iter() {
        transcript.append_scalar(b"Scalar", &scalar);
    }

    // Squeeze a challenge and compare them to one another
    let challenge = transcript.challenge_scalar(b"Challenge");
    let counterparty_challenge = fabric.exchange_value(challenge.clone());

    let challenge1 = await_result(challenge);
    let challenge2 = await_result(counterparty_challenge);

    assert_scalars_eq(&challenge1, &challenge2)
}

/// Tests adding many points to the transcript
fn test_add_points(test_args: &IntegrationTestArgs) -> Result<(), String> {
    let fabric = &test_args.mpc_fabric;

    let n = 10;
    let my_points = (0..n).map(|_| random_point()).collect_vec();

    // Share with the counterparty
    let party0_points = my_points
        .iter()
        .map(|p| fabric.share_point(*p, PARTY0))
        .collect_vec();
    let party1_points = my_points
        .iter()
        .map(|p| fabric.share_point(*p, PARTY1))
        .collect_vec();

    // Open all points and append them to the transcript
    let opened_points = party0_points
        .iter()
        .chain(party1_points.iter())
        .map(|p| p.open_authenticated())
        .map(|p| p.value)
        .collect_vec();

    let mut transcript = MpcTranscript::new(Transcript::new(b"test"), fabric.clone());
    for point in opened_points.into_iter() {
        transcript.append_point(b"Point", &point);
    }

    let challenge = transcript.challenge_scalar(b"Challenge");
    let counterparty_challenge = fabric.exchange_value(challenge.clone());

    let challenge1 = await_result(challenge);
    let challenge2 = await_result(counterparty_challenge);

    assert_scalars_eq(&challenge1, &challenge2)
}

inventory::submit!(IntegrationTest {
    name: "transcript::test_add_scalars",
    test_fn: test_add_scalars,
});

inventory::submit!(IntegrationTest {
    name: "transcript::test_add_points",
    test_fn: test_add_points,
});
