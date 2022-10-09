use std::iter;

use bulletproofs::{
    r1cs::{R1CSError, RandomizableConstraintSystem, Variable, Verifier},
    r1cs_mpc::{
        mpc_constraint_system::MpcRandomizableConstraintSystem,
        mpc_linear_combination::MpcVariable, mpc_prover::MpcProver, proof::SharedR1CSProof,
    },
    BulletproofGens, PedersenGens,
};
use curve25519_dalek::scalar::Scalar;

use itertools::Itertools;
use merlin::Transcript;
use mpc_ristretto::{
    authenticated_ristretto::{AuthenticatedCompressedRistretto, AuthenticatedRistretto},
    beaver::SharedValueSource,
    network::MpcNetwork,
};
use rand::{CryptoRng, RngCore};
use rand_core::OsRng;

use crate::{
    mpc_inner_product::TRANSCRIPT_SEED, IntegrationTest, IntegrationTestArgs, SharedMpcFabric,
};

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

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> SimpleCircuit<N, S> {
    /// Gadget that applies constraints to the constraint system
    fn gadget<CS: MpcRandomizableConstraintSystem<N, S>>(
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

/// Tests that proving a simple statement works properly
fn test_simple_r1cs(test_args: &IntegrationTestArgs) -> Result<(), String> {
    // Setup

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

inventory::submit!(IntegrationTest {
    name: "mpc-prover::test_simple_r1cs",
    test_fn: test_simple_r1cs
});
