#![allow(unused_doc_comments)]

use futures::future::join_all;
use mpc_bulletproof::{
    r1cs::{
        ConstraintSystem, R1CSError, RandomizableConstraintSystem, RandomizedConstraintSystem,
        Variable, Verifier,
    },
    r1cs_mpc::{
        MpcConstraintSystem, MpcProver, MpcRandomizableConstraintSystem,
        MpcRandomizedConstraintSystem, MpcVariable, MultiproverError, PartiallySharedR1CSProof,
    },
    BulletproofGens, PedersenGens,
};

use itertools::Itertools;
use merlin::Transcript;
use mpc_stark::{
    algebra::{
        authenticated_stark_point::AuthenticatedStarkPointOpenResult, scalar::Scalar,
        stark_curve::StarkPoint,
    },
    error::MpcError,
    MpcFabric, PARTY0, PARTY1,
};
use rand::rngs::OsRng;
use tokio::runtime::Handle;

use crate::{mpc_inner_product::TRANSCRIPT_SEED, IntegrationTest, IntegrationTestArgs};

/// A helper macro to await a vector of results by blocking the runtime
macro_rules! await_vec {
    ($vec:expr) => {{
        Handle::current().block_on(join_all($vec))
    }};
}

/// Implements a multiplication between two dot products of vectors \vec{a} and \vec{b}
/// Result is `c`
struct SimpleCircuit;

impl<'a> SimpleCircuit {
    /// Gadget that applies constraints to the constraint system
    fn gadget<CS: MpcRandomizableConstraintSystem<'a>>(
        cs: &mut CS,
        a: Vec<MpcVariable>,
        b: Vec<MpcVariable>,
        expected_out: MpcVariable,
    ) -> Result<(), R1CSError> {
        // Statement is (5 * a1 + 10 * a2) * (2 * b1 + 3 * b2) == 920
        let (_, _, mul_out) = cs
            .multiply(
                &(Scalar::from(5u64) * &a[0] + Scalar::from(10u64) * &a[1]),
                &(Scalar::from(2u64) * &b[0] + Scalar::from(3u64) * &b[1]),
            )
            .unwrap();

        cs.constrain(mul_out - expected_out);

        Ok(())
    }

    fn single_prover_gadget<CS: RandomizableConstraintSystem>(
        cs: &mut CS,
        a: Vec<Variable>,
        b: Vec<Variable>,
        expected_out: Variable,
    ) -> Result<(), R1CSError> {
        // Statement is (5 * a1 + 10 * a2) * (2 * b1 + 3 * b2) == 920
        let (_, _, mul_out) = cs.multiply(
            Scalar::from(5u64) * a[0] + Scalar::from(10u64) * a[1],
            Scalar::from(2u64) * b[0] + Scalar::from(3u64) * b[1],
        );

        cs.constrain(mul_out - expected_out);

        Ok(())
    }

    /// Create a bulletproof fo the statement specified by `gadget`
    #[allow(clippy::type_complexity)]
    pub fn prove<'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        a: &[Scalar],
        b: &[Scalar],
        expected_out: Scalar,
        mpc_fabric: MpcFabric,
    ) -> Result<
        (
            PartiallySharedR1CSProof,
            Vec<AuthenticatedStarkPointOpenResult>, // `a` commitments
            Vec<AuthenticatedStarkPointOpenResult>, // `b` commitments
            AuthenticatedStarkPointOpenResult,      // `c` commitments
        ),
        String,
    > {
        assert_eq!(a.len(), 2);
        assert_eq!(a.len(), b.len());

        // Setup
        let mut rng = OsRng {};

        // Create the proof system
        let prover_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
        let mut prover = MpcProver::new_with_fabric(mpc_fabric, prover_transcript, pc_gens);

        let (a_commit, a_vars) = prover
            .batch_commit(
                PARTY0,
                a.iter().copied(),
                &[Scalar::random(&mut rng), Scalar::random(&mut rng)],
            )
            .map_err(|err| format!("Error committing input values: {:?}", err))?;

        let (b_commit, b_vars) = prover
            .batch_commit(
                PARTY1,
                b.iter().copied(),
                &[Scalar::random(&mut rng), Scalar::random(&mut rng)],
            )
            .map_err(|err| format!("error sharing values: {:?}", err))?;

        let (c_commit, c_var) = prover
            .commit(0 /* owning_party */, expected_out, Scalar::from(1))
            .map_err(|err| format!("Error committing to output: {:?}", err))?;

        // Apply the gadget to generate the constraints, then prove
        Self::gadget(&mut prover, a_vars, b_vars, c_var)
            .map_err(|err| format!("Error building constraints: {:?}", err))?;
        let proof = prover
            .prove(bp_gens)
            .map_err(|err| format!("Error proving: {:?}", err))?;

        Ok((proof, a_commit, b_commit, c_commit))
    }

    /// Verify a proof of the execution
    pub fn verify(
        proof: PartiallySharedR1CSProof,
        a_commit: Vec<AuthenticatedStarkPointOpenResult>,
        b_commit: Vec<AuthenticatedStarkPointOpenResult>,
        c_commit: AuthenticatedStarkPointOpenResult,
    ) -> Result<(), MultiproverError> {
        let pc_gens = PedersenGens::default();
        let bp_gens =
            BulletproofGens::new(1024 /* gens_capacity */, 1 /* party_capacity */);

        // Open the proof and the commitments
        let opened_proof = proof.open()?;
        let opened_a_comms: Vec<StarkPoint> = await_vec!(a_commit)
            .into_iter()
            .collect::<Result<Vec<_>, _>>()
            .map_err(MultiproverError::Mpc)?;
        let opened_b_comms: Vec<StarkPoint> = await_vec!(b_commit)
            .into_iter()
            .collect::<Result<Vec<_>, _>>()
            .map_err(MultiproverError::Mpc)?;
        let opened_c_comm: StarkPoint = await_vec!(vec![c_commit])
            .remove(0)
            .map_err(MultiproverError::Mpc)?;

        // Build the verifier
        let mut verifier_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
        let mut verifier = Verifier::new(&pc_gens, &mut verifier_transcript);

        // Build commitments to the verifier inputs
        let a_input = opened_a_comms
            .iter()
            .map(|x| verifier.commit(*x))
            .collect_vec();

        let b_input = opened_b_comms
            .iter()
            .map(|x| verifier.commit(*x))
            .collect_vec();

        let c_input = verifier.commit(opened_c_comm);

        Self::single_prover_gadget(&mut verifier, a_input, b_input, c_input)
            .map_err(MultiproverError::ProverError)?;

        verifier
            .verify(&opened_proof, &bp_gens)
            .map_err(MultiproverError::ProverError)
    }
}

// ---------
// | Tests |
// ---------

/// Tests that proving a simple statement works properly
fn test_simple_r1cs(test_args: &IntegrationTestArgs) -> Result<(), String> {
    // Both parties commit to their inputs
    // Party 0 holds (a1, a2), party 1 holds (b1, b2)
    let my_values = if test_args.party_id == 0 {
        [2u64, 3u64]
    } else {
        [4u64, 5u64]
    };
    let my_scalars: Vec<Scalar> = my_values.into_iter().map(Scalar::from).collect();

    // Commit and share values
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(2, 1);

    let (proof, a_commit, b_commit, c_commit) = SimpleCircuit::prove(
        &pc_gens,
        &bp_gens,
        &my_scalars,
        &my_scalars,
        Scalar::from(920u64), // Expected value of the statement defined by the gadget
        test_args.mpc_fabric.clone(),
    )?;

    SimpleCircuit::verify(proof, a_commit, b_commit, c_commit)
        .map_err(|err| format!("Verification error: {err:?}"))
}

/// Tests the case in which the parties hold interleaved witness variables
fn test_r1cs_interleaved_witness(test_args: &IntegrationTestArgs) -> Result<(), String> {
    // Setup
    let mut rng = OsRng {};
    #[allow(clippy::if_same_then_else)]
    let my_values = if test_args.party_id == 0 {
        [2u64 /* a1 */, 4u64 /* b2 */]
    } else {
        [6u64 /* a2 */, 8u64 /* b1 */]
    };

    let my_scalars = my_values.iter().map(|v| Scalar::from(*v)).collect_vec();

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(2, 1);

    // Party 0 holds (a1, b2), party 1 holds (a2, b1)
    // Create the proof system
    let prover_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
    let mut prover =
        MpcProver::new_with_fabric(test_args.mpc_fabric.clone(), prover_transcript, &pc_gens);

    let (party0_commit, party0_vars) = prover
        .batch_commit(
            0, /* owning_party */
            my_scalars.clone(),
            &[Scalar::random(&mut rng), Scalar::random(&mut rng)],
        )
        .map_err(|err| format!("Error committing input values: {:?}", err))?;

    let (party1_commit, party1_vars) = prover
        .batch_commit(
            1, /* owning_party */
            my_scalars,
            &[Scalar::random(&mut rng), Scalar::random(&mut rng)],
        )
        .map_err(|err| format!("error sharing values: {:?}", err))?;

    let (c_commit, c_var) = prover
        .commit(
            0, /* owning_party */
            Scalar::from(1960u64),
            Scalar::random(&mut rng),
        )
        .map_err(|err| format!("Error committing to output: {:?}", err))?;

    // Apply the gadget to generate the constraints, then prove
    SimpleCircuit::gadget(
        &mut prover,
        vec![party0_vars[0].clone(), party1_vars[0].clone()],
        vec![party1_vars[1].clone(), party0_vars[1].clone()],
        c_var,
    )
    .map_err(|err| format!("Error building constraints: {:?}", err))?;

    let proof = prover
        .prove(&bp_gens)
        .map_err(|err| format!("Error proving: {:?}", err))?
        .open()
        .map_err(|err| format!("Error opening proof: {:?}", err))?;

    // Build a verifier
    let mut verifier_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
    let mut verifier = Verifier::new(&pc_gens, &mut verifier_transcript);

    // Commit to the values in the verifier
    let party0_vars = await_vec!(party0_commit)
        .into_iter()
        .map(|x| x.map(|val| verifier.commit(val)))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|err| format!("Error opening `a` commitments: {:?}", err))?;
    let party1_vars = await_vec!(party1_commit)
        .into_iter()
        .map(|x| x.map(|val| verifier.commit(val)))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|err| format!("Error opening `b` commitments: {:?}", err))?;

    let c_var = await_vec!(vec![c_commit])
        .pop()
        .unwrap()
        .map(|val| verifier.commit(val))
        .map_err(|err| format!("Error opening `c` commitment: {:?}", err))?;

    SimpleCircuit::single_prover_gadget(
        &mut verifier,
        vec![party0_vars[0], party1_vars[0]],
        vec![party1_vars[1], party0_vars[1]],
        c_var,
    )
    .map_err(|err| format!("Error specifying verifier constraints: {:?}", err))?;

    verifier
        .verify(&proof, &bp_gens)
        .map_err(|err| format!("Verification error: {:?}", err))
}

fn test_r1cs_proof_malleability(test_args: &IntegrationTestArgs) -> Result<(), String> {
    // Both parties commit to their inputs
    // Party 0 holds (a1, a2), party 1 holds (b1, b2)
    let my_values = if test_args.party_id == 0 {
        [2u64, 3u64]
    } else {
        [4u64, 5u64]
    };
    let my_scalars: Vec<Scalar> = my_values.into_iter().map(Scalar::from).collect();

    // Commit and share values
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(2, 1);

    let (mut proof, _, _, _) = SimpleCircuit::prove(
        &pc_gens,
        &bp_gens,
        &my_scalars,
        &my_scalars,
        Scalar::from(920u64), // Expected value of the statement defined by the gadget
        test_args.mpc_fabric.clone(),
    )?;

    // Party 1 tries to corrupt the proof
    if test_args.party_id == 1 {
        proof.ipp_proof.a = proof.ipp_proof.a + Scalar::from(10u64);
    } else {
        // Party 2 must perform an operation to keep the computation graphs in sync
        proof.ipp_proof.a = proof.ipp_proof.a + Scalar::from(0)
    }

    // Verify that opening the proof fails
    proof
        .open()
        .err()
        .map(|err| match err {
            MultiproverError::Mpc(MpcError::AuthenticationError) => Ok(()),
            _ => Err(err.to_string()),
        })
        .unwrap_or(Err(
            "expected authentication error, but proof opened correctly".to_string(),
        ))
}

/// A shuffle proof proves that `x` is a permutation of `y`
pub struct ShuffleProof;

impl<'a> ShuffleProof {
    fn gadget<'b, CS: MpcRandomizableConstraintSystem<'a>>(
        cs: &'b mut CS,
        x: Vec<MpcVariable>,
        y: Vec<MpcVariable>,
    ) -> Result<(), String> {
        assert_eq!(x.len(), y.len());
        let k = x.len();
        if k == 1 {
            cs.constrain(&y[0] - &x[0]);
            return Ok(());
        }

        cs.specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"shuffle challenge");

            let (_, _, last_mulx_out) = cs.multiply(&(&x[k - 1] - &z), &(&x[k - 2] - &z)).unwrap();
            let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |acc, i| {
                let (_, _, o) = cs.multiply(&acc.into(), &(&x[i] - &z)).unwrap();
                o
            });

            let (_, _, last_muly_out) = cs.multiply(&(&y[k - 1] - &z), &(&y[k - 2] - &z)).unwrap();
            let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |acc, i| {
                let (_, _, o) = cs.multiply(&acc.into(), &(&y[i] - &z)).unwrap();
                o
            });

            cs.constrain(first_mulx_out - first_muly_out);

            Ok(())
        })
        .map_err(|err| format!("Error building constraints: {:?}", err))?;

        Ok(())
    }

    fn single_prover_gadget<CS: RandomizableConstraintSystem>(
        cs: &mut CS,
        x: Vec<Variable>,
        y: Vec<Variable>,
    ) -> Result<(), R1CSError> {
        assert_eq!(x.len(), y.len());
        let k = x.len();

        if k == 1 {
            cs.constrain(y[0] - x[0]);
            return Ok(());
        }

        cs.specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"shuffle challenge");
            let (_, _, last_mulx_out) = cs.multiply(x[k - 1] - z, x[k - 2] - z);
            let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |acc, i| {
                let (_, _, o) = cs.multiply(acc.into(), x[i] - z);
                o
            });

            let (_, _, last_muly_out) = cs.multiply(y[k - 1] - z, y[k - 2] - z);
            let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |acc, i| {
                let (_, _, o) = cs.multiply(acc.into(), y[i] - z);
                o
            });

            cs.constrain(first_mulx_out - first_muly_out);

            Ok(())
        })?;

        Ok(())
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn prove(
        x: &[Scalar],
        y: &[Scalar],
        pc_gens: &PedersenGens,
        bp_gens: &BulletproofGens,
        mpc_fabric: MpcFabric,
    ) -> Result<
        (
            PartiallySharedR1CSProof,
            Vec<AuthenticatedStarkPointOpenResult>, // `x` commitments
            Vec<AuthenticatedStarkPointOpenResult>, // `y` commitments
        ),
        String,
    > {
        assert_eq!(x.len(), y.len());

        // Setup
        let mut rng = OsRng {};

        // Build the prover
        let prover_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
        let mut prover = MpcProver::new_with_fabric(mpc_fabric, prover_transcript, pc_gens);

        // Commit to the inputs
        let (x_commit, x_vars) = prover
            .batch_commit(
                PARTY0,
                x.iter().copied(),
                &(0..x.len()).map(|_| Scalar::random(&mut rng)).collect_vec(),
            )
            .map_err(|err| format!("Error committing to `x` values: {:?}", err))?;

        let (y_commit, y_vars) = prover
            .batch_commit(
                PARTY1,
                y.iter().copied(),
                &(0..y.len()).map(|_| Scalar::random(&mut rng)).collect_vec(),
            )
            .map_err(|err| format!("Error committing to `y` values: {:?}", err))?;

        // Apply the gadget to specify the constraints and prove the statement
        Self::gadget(&mut prover, x_vars, y_vars)
            .map_err(|err| format!("Error specifying constraints: {:?}", err))?;

        let proof = prover
            .prove(bp_gens)
            .map_err(|err| format!("Error proving: {:?}", err))?;

        Ok((proof, x_commit, y_commit))
    }

    pub(crate) fn verify(
        proof: PartiallySharedR1CSProof,
        x_commit: Vec<AuthenticatedStarkPointOpenResult>,
        y_commit: Vec<AuthenticatedStarkPointOpenResult>,
    ) -> Result<(), MultiproverError> {
        // Setup
        let pc_gens = PedersenGens::default();
        let bp_gens =
            BulletproofGens::new(1024 /* gens_capacity */, 1 /* party_capacity */);

        // Open the proof and the commitments
        let opened_proof = proof.open()?;
        let opened_x = await_vec!(x_commit)
            .into_iter()
            .collect::<Result<Vec<_>, _>>()
            .map_err(MultiproverError::Mpc)?;
        let opened_y = await_vec!(y_commit)
            .into_iter()
            .collect::<Result<Vec<_>, _>>()
            .map_err(MultiproverError::Mpc)?;

        // Build the verifier
        let mut verifier_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
        let mut verifier = Verifier::new(&pc_gens, &mut verifier_transcript);

        // Commit to the inputs in the verifier
        let x_input = opened_x.iter().map(|x| verifier.commit(*x)).collect_vec();
        let y_input = opened_y.iter().map(|y| verifier.commit(*y)).collect_vec();

        Self::single_prover_gadget(&mut verifier, x_input, y_input)
            .map_err(MultiproverError::ProverError)?;

        verifier
            .verify(&opened_proof, &bp_gens)
            .map_err(MultiproverError::ProverError)
    }
}

/// Tests the second phase commitments + constraints in the MPC system
fn test_shuffle_proof(test_args: &IntegrationTestArgs) -> Result<(), String> {
    // Values, for the sake of this test the permutation is a reversal
    let k = 8;
    let my_values = if test_args.party_id == 0 {
        (0u64..k).collect_vec()
    } else {
        (0u64..k).rev().collect_vec()
    };
    let my_scalars = my_values.into_iter().map(Scalar::from).collect_vec();

    // Setup
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(
        2 * k as usize, /* gens_capacity */
        1,              /* party_capacity */
    );

    let (proof, x_commit, y_commit) = ShuffleProof::prove(
        &my_scalars,
        &my_scalars,
        &pc_gens,
        &bp_gens,
        test_args.mpc_fabric.clone(),
    )?;

    ShuffleProof::verify(proof, x_commit, y_commit)
        .map_err(|err| format!("Verification error: {err:?}"))
}

/// Tests that a false statement fails verification
fn test_false_shuffle(test_args: &IntegrationTestArgs) -> Result<(), String> {
    let k = 8;
    let mut rng = OsRng {};
    let my_values = (0u64..k).map(|_| Scalar::random(&mut rng)).collect_vec();

    // Setup
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(
        2 * k as usize, /* gens_capacity */
        1,              /* party_capacity */
    );

    let (proof, x_commit, y_commit) = ShuffleProof::prove(
        &my_values,
        &my_values,
        &pc_gens,
        &bp_gens,
        test_args.mpc_fabric.clone(),
    )?;

    ShuffleProof::verify(proof, x_commit, y_commit)
        .err()
        .map(|err| {
            if let MultiproverError::ProverError(R1CSError::VerificationError) = err {
                Ok(())
            } else {
                Err(format!("Expected verification error, got {:?}", err))
            }
        })
        .unwrap_or(Err("Expected verification error, got Ok".to_string()))
}

// ------------------
// | Take Inventory |
// ------------------

inventory::submit!(IntegrationTest {
    name: "mpc-prover::test_simple_r1cs",
    test_fn: test_simple_r1cs
});

inventory::submit!(IntegrationTest {
    name: "mpc-prover::test_r1cs_interleaved_witness",
    test_fn: test_r1cs_interleaved_witness,
});

inventory::submit!(IntegrationTest {
    name: "mpc-prover::test_r1cs_proof_malleability",
    test_fn: test_r1cs_proof_malleability,
});

inventory::submit!(IntegrationTest {
    name: "mpc-prover::test_shuffle_proof",
    test_fn: test_shuffle_proof,
});

inventory::submit!(IntegrationTest {
    name: "mpc-prover::test_false_shuffle",
    test_fn: test_false_shuffle,
});
