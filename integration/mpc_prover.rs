#![allow(unused_doc_comments)]
use std::iter;

use bulletproofs::{
    r1cs::{
        ConstraintSystem, R1CSError, RandomizableConstraintSystem, RandomizedConstraintSystem,
        Variable, Verifier,
    },
    r1cs_mpc::{
        MpcConstraintSystem, MpcProver, MpcRandomizableConstraintSystem,
        MpcRandomizedConstraintSystem, MpcVariable, SharedR1CSProof,
    },
    BulletproofGens, PedersenGens,
};
use curve25519_dalek::scalar::Scalar;

use itertools::Itertools;
use merlin::Transcript;
use mpc_ristretto::{
    authenticated_ristretto::{AuthenticatedCompressedRistretto, AuthenticatedRistretto},
    beaver::SharedValueSource,
    network::{MpcNetwork, QuicTwoPartyNet},
};
use rand::{CryptoRng, RngCore};
use rand_core::OsRng;

use crate::{
    mpc_inner_product::TRANSCRIPT_SEED, IntegrationTest, IntegrationTestArgs, PartyIDBeaverSource,
    SharedMpcFabric,
};

/**
 * Helpers
 */

pub(crate) struct RandomScalarGenerator<'a, T: RngCore + CryptoRng> {
    rng: &'a mut T,
}

impl<'a, T: RngCore + CryptoRng> RandomScalarGenerator<'a, T> {
    fn new(rng: &'a mut T) -> Self {
        Self { rng }
    }
}

impl<'a, T: RngCore + CryptoRng> Iterator for RandomScalarGenerator<'a, T> {
    type Item = Scalar;

    fn next(&mut self) -> Option<Self::Item> {
        Some(Scalar::random(self.rng))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// Implements a multiplication between two dot products of vectors \vec{a} and \vec{b}
/// Result is `c`
struct SimpleCircuit<N: MpcNetwork + Send, S: SharedValueSource<Scalar>>(SharedR1CSProof<N, S>);

impl<'s, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> SimpleCircuit<N, S> {
    /// Gadget that applies constraints to the constraint system
    fn gadget<CS: MpcRandomizableConstraintSystem<'s, N, S>>(
        cs: &mut CS,
        a: Vec<MpcVariable<N, S>>,
        b: Vec<MpcVariable<N, S>>,
        expected_out: MpcVariable<N, S>,
    ) -> Result<(), R1CSError> {
        // Statment is (5 * a1 + 10 * a2) * (2 * b1 + 3 * b2) == 920
        let (_, _, mul_out) = cs.multiply(
            Scalar::from(5u64) * &a[0] + Scalar::from(10u64) * &a[1],
            Scalar::from(2u64) * &b[0] + Scalar::from(3u64) * &b[1],
        );

        cs.constrain(mul_out - expected_out);

        Ok(())
    }

    fn single_prover_gadget<CS: RandomizableConstraintSystem>(
        cs: &mut CS,
        a: Vec<Variable>,
        b: Vec<Variable>,
        expected_out: Variable,
    ) -> Result<(), R1CSError> {
        // Statment is (5 * a1 + 10 * a2) * (2 * b1 + 3 * b2) == 920
        let (_, _, mul_out) = cs.multiply(
            Scalar::from(5u64) * a[0] + Scalar::from(10u64) * a[1],
            Scalar::from(2u64) * b[0] + Scalar::from(3u64) * b[1],
        );

        cs.constrain(mul_out - expected_out);

        Ok(())
    }

    /// Create a bulletproof fo the statement specified by `gadget`
    #[allow(clippy::type_complexity)]
    pub fn prove<'a>(
        pc_gens: &'a PedersenGens,
        bp_gens: &'a BulletproofGens,
        a: &[Scalar],
        b: &[Scalar],
        expected_out: Scalar,
        mpc_fabric: SharedMpcFabric<N, S>,
    ) -> Result<
        (
            SimpleCircuit<N, S>,
            Vec<AuthenticatedCompressedRistretto<N, S>>, // `a` commitments
            Vec<AuthenticatedCompressedRistretto<N, S>>, // `b` commitments
            AuthenticatedCompressedRistretto<N, S>,      // `c` commitments
        ),
        String,
    > {
        assert_eq!(a.len(), 2);
        assert_eq!(a.len(), b.len());

        // Setup
        let mut rng = OsRng {};
        let mut random_scalar_chain = RandomScalarGenerator::new(&mut rng);

        let blinders = [
            random_scalar_chain.next().unwrap(),
            random_scalar_chain.next().unwrap(),
            random_scalar_chain.next().unwrap(),
        ];

        // Create the proof system
        let mut prover_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
        let mut prover = MpcProver::new_with_fabric(mpc_fabric, &mut prover_transcript, pc_gens);

        let (a_commit, a_vars) = prover
            .batch_commit(0 /* owning_party */, a, &blinders[..2])
            .map_err(|err| format!("Error committing input values: {:?}", err))?;

        let (b_commit, b_vars) = prover
            .batch_commit(1 /* owning_party */, b, &blinders[..2])
            .map_err(|err| format!("error sharing values: {:?}", err))?;

        let (c_commit, c_var) = prover
            .commit(0 /* owning_party */, expected_out, blinders[2])
            .map_err(|err| format!("Error commiting to output: {:?}", err))?;

        // Apply the gadget to generate the constraints, then prove
        Self::gadget(&mut prover, a_vars, b_vars, c_var)
            .map_err(|err| format!("Error building constraints: {:?}", err))?;
        let proof = prover
            .prove(bp_gens)
            .map_err(|err| format!("Error proving: {:?}", err))?;

        Ok((Self(proof), a_commit, b_commit, c_commit))
    }

    /// Verify a proof of the execution
    pub fn verify<'a>(
        &self,
        pc_gens: &'a PedersenGens,
        bp_gens: &'a BulletproofGens,
        a_commit: &Vec<AuthenticatedCompressedRistretto<N, S>>,
        b_commit: &Vec<AuthenticatedCompressedRistretto<N, S>>,
        c_commit: &AuthenticatedCompressedRistretto<N, S>,
    ) -> Result<(), String> {
        // Open the proof and the commitments
        let opened_proof = self
            .0
            .open()
            .map_err(|err| format!("Error opening proof: {:?}", err))?;

        let opened_commitments = AuthenticatedRistretto::batch_open_and_authenticate(
            &a_commit
                .iter()
                .chain(b_commit.iter())
                .chain(iter::once(c_commit))
                .map(|x| x.decompress().unwrap())
                .collect_vec(),
        )
        .map_err(|err| format!("Error opening commitments: {:?}", err))?;

        let opened_a_commit = &opened_commitments[..a_commit.len()];
        let opened_b_commit = &opened_commitments[a_commit.len()..a_commit.len() + b_commit.len()];
        let opened_c_commit = &opened_commitments[opened_commitments.len() - 1];

        // Build the verifier
        let mut verifier_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
        let mut verifier = Verifier::new(&mut verifier_transcript);

        // Build commitments to the verifier inputs
        let a_input = opened_a_commit
            .iter()
            .map(|x| verifier.commit(x.compress().value()))
            .collect_vec();

        let b_input = opened_b_commit
            .iter()
            .map(|x| verifier.commit(x.compress().value()))
            .collect_vec();

        let c_input = verifier.commit(opened_c_commit.compress().value());

        Self::single_prover_gadget(&mut verifier, a_input, b_input, c_input)
            .map_err(|err| format!("Error applying constraints to verifier: {:?}", err))?;

        verifier
            .verify(&opened_proof, pc_gens, bp_gens)
            .map_err(|err| format!("Error verifying proof: {:?}", err))
    }
}

/**
 * Tests
 */

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

    proof.verify(&pc_gens, &bp_gens, &a_commit, &b_commit, &c_commit)
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
    let mut prover_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
    let mut prover = MpcProver::new_with_fabric(
        test_args.mpc_fabric.clone(),
        &mut prover_transcript,
        &pc_gens,
    );

    // Commit to input and result values
    let mut random_scalar_chain = RandomScalarGenerator::new(&mut rng);
    let blinders = [
        random_scalar_chain.next().unwrap(),
        random_scalar_chain.next().unwrap(),
        random_scalar_chain.next().unwrap(),
    ];

    let (party0_commit, party0_vars) = prover
        .batch_commit(0 /* owning_party */, &my_scalars, &blinders[..2])
        .map_err(|err| format!("Error committing input values: {:?}", err))?;

    let (party1_commit, party1_vars) = prover
        .batch_commit(1 /* owning_party */, &my_scalars, &blinders[..2])
        .map_err(|err| format!("error sharing values: {:?}", err))?;

    let (c_commit, c_var) = prover
        .commit(
            0, /* owning_party */
            Scalar::from(1960u64),
            blinders[2],
        )
        .map_err(|err| format!("Error commiting to output: {:?}", err))?;

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
    let mut verifier = Verifier::new(&mut verifier_transcript);

    // Commit to the values in the verifier
    let verifier_party0_vars = party0_commit
        .iter()
        .map(|commit| {
            verifier.commit(
                commit
                    .decompress()
                    .unwrap()
                    .open_and_authenticate()
                    .unwrap()
                    .compress()
                    .value(),
            )
        })
        .collect_vec();

    let verifier_party1_vars = party1_commit
        .iter()
        .map(|v| {
            verifier.commit(
                v.decompress()
                    .unwrap()
                    .open_and_authenticate()
                    .unwrap()
                    .compress()
                    .value(),
            )
        })
        .collect_vec();

    let verifier_c_var = verifier.commit(
        c_commit
            .decompress()
            .unwrap()
            .open_and_authenticate()
            .unwrap()
            .compress()
            .value(),
    );

    SimpleCircuit::<QuicTwoPartyNet, PartyIDBeaverSource>::single_prover_gadget(
        &mut verifier,
        vec![verifier_party0_vars[0], verifier_party1_vars[0]],
        vec![verifier_party1_vars[1], verifier_party0_vars[1]],
        verifier_c_var,
    )
    .map_err(|err| format!("Error specifying verifier constraints: {:?}", err))?;

    verifier
        .verify(&proof, &pc_gens, &bp_gens)
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
        proof.0.ipp_proof.a += Scalar::from(10u64);
    }
    proof.0.open().map_or(Ok(()), |_| {
        Err("Expected authentication failure, authentication passed...".to_string())
    })
}

/// A shuffle proof proves that `x` is a permutation of `y`
pub struct ShuffleProof<N: MpcNetwork + Send, S: SharedValueSource<Scalar>>(SharedR1CSProof<N, S>);

impl<'a, N: MpcNetwork + Send + 'a, S: SharedValueSource<Scalar> + 'a> ShuffleProof<N, S> {
    fn gadget<'b, CS: MpcRandomizableConstraintSystem<'a, N, S>>(
        cs: &'b mut CS,
        x: Vec<MpcVariable<N, S>>,
        y: Vec<MpcVariable<N, S>>,
    ) -> Result<(), String>
    where
        'a: 'b,
    {
        assert_eq!(x.len(), y.len());
        let k = x.len();

        if k == 1 {
            cs.constrain(&y[0] - &x[0]);
            return Ok(());
        }

        cs.specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"shuffle challenge");

            let (_, _, last_mulx_out) = cs.multiply(&x[k - 1] - z, &x[k - 2] - z);
            let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |acc, i| {
                let (_, _, o) = cs.multiply(acc.into(), &x[i] - z);
                o
            });

            let (_, _, last_muly_out) = cs.multiply(&y[k - 1] - z, &y[k - 2] - z);
            let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |acc, i| {
                let (_, _, o) = cs.multiply(acc.into(), &y[i] - z);
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
    ) -> Result<(), String> {
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
        })
        .map_err(|err| format!("Error building constraints: {:?}", err))?;

        Ok(())
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn prove(
        x: &[Scalar],
        y: &[Scalar],
        pc_gens: &PedersenGens,
        bp_gens: &BulletproofGens,
        mpc_fabric: SharedMpcFabric<N, S>,
    ) -> Result<
        (
            Self,
            Vec<AuthenticatedCompressedRistretto<N, S>>, // `x` commitments
            Vec<AuthenticatedCompressedRistretto<N, S>>, // `y` commitments
        ),
        String,
    > {
        assert_eq!(x.len(), y.len());

        // Setup
        let mut rng = OsRng {};
        let mut random_scalar_chain = RandomScalarGenerator::new(&mut rng);

        let blinders = (0..x.len() * 2)
            .map(|_| random_scalar_chain.next().unwrap())
            .collect_vec();

        // Build the prover
        let mut prover_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
        let mut prover = MpcProver::new_with_fabric(mpc_fabric, &mut prover_transcript, pc_gens);

        // Commit to the inputs
        let (x_commit, x_vars) = prover
            .batch_commit(0 /* owning_party */, x, &blinders[0..x.len()])
            .map_err(|err| format!("Error committing to `x` values: {:?}", err))?;

        let (y_commit, y_vars) = prover
            .batch_commit(1 /* owning_party */, y, &blinders[x.len()..])
            .map_err(|err| format!("Error committing to `y` values: {:?}", err))?;

        // Apply the gadget to specify the constraints and prove the statement
        Self::gadget(&mut prover, x_vars, y_vars)
            .map_err(|err| format!("Error specifying constraints: {:?}", err))?;

        let proof = prover
            .prove(bp_gens)
            .map_err(|err| format!("Error proving: {:?}", err))?;

        Ok((Self(proof), x_commit, y_commit))
    }

    pub(crate) fn verify<'b>(
        &self,
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        x_commit: &[AuthenticatedCompressedRistretto<N, S>],
        y_commit: &[AuthenticatedCompressedRistretto<N, S>],
    ) -> Result<(), String> {
        // Open the proof and the commitments
        let opened_proof = self
            .0
            .open()
            .map_err(|err| format!("Error opening proof: {:?}", err))?;

        let opened_commitments = AuthenticatedRistretto::batch_open_and_authenticate(
            &x_commit
                .iter()
                .chain(y_commit.iter())
                .map(|x| x.decompress().unwrap())
                .collect_vec(),
        )
        .map_err(|err| format!("Error opening commitments: {:?}", err))?;

        let opened_x_commit = &opened_commitments[..x_commit.len()];
        let opened_y_commit = &opened_commitments[x_commit.len()..];

        // Build the verifier
        let mut verifier_transcript = Transcript::new(TRANSCRIPT_SEED.as_bytes());
        let mut verifier = Verifier::new(&mut verifier_transcript);

        // Commit to the inputs in the verifier
        let x_input = opened_x_commit
            .iter()
            .map(|x| verifier.commit(x.compress().value()))
            .collect_vec();
        let y_input = opened_y_commit
            .iter()
            .map(|y| verifier.commit(y.compress().value()))
            .collect_vec();

        Self::single_prover_gadget(&mut verifier, x_input, y_input)
            .map_err(|err| format!("Error specifying constraints for verifier: {:?}", err))?;

        verifier
            .verify(&opened_proof, pc_gens, bp_gens)
            .map_err(|err| format!("Error verifying proof: {:?}", err))
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

    proof.verify(&pc_gens, &bp_gens, &x_commit, &y_commit)
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

    proof
        .verify(&pc_gens, &bp_gens, &x_commit, &y_commit)
        .map_or(Ok(()), |_| {
            Err("Expected verification failure, verification passed...".to_string())
        })
}

/**
 * Take inventory
 */

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
