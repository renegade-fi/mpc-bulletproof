#![allow(non_snake_case)]

extern crate lazy_static;
extern crate merlin;
extern crate mpc_bulletproof;
extern crate rand;

use lazy_static::lazy_static;
use merlin::HashChainTranscript as Transcript;
use mpc_bulletproof::r1cs::*;
use mpc_bulletproof::{BulletproofGens, PedersenGens};
use mpc_stark::algebra::scalar::Scalar;
use mpc_stark::algebra::stark_curve::StarkPoint;
use rand::seq::SliceRandom;
use rand::thread_rng;

// Shuffle gadget (documented in markdown file)

/// A proof-of-shuffle.
struct ShuffleProof(R1CSProof);

impl ShuffleProof {
    fn gadget<CS: RandomizableConstraintSystem>(
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

            // Make last x multiplier for i = k-1 and k-2
            let (_, _, last_mulx_out) = cs.multiply(x[k - 1] - z, x[k - 2] - z);

            // Make multipliers for x from i == [0, k-3]
            let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
                let (_, _, o) = cs.multiply(prev_out.into(), x[i] - z);
                o
            });

            // Make last y multiplier for i = k-1 and k-2
            let (_, _, last_muly_out) = cs.multiply(y[k - 1] - z, y[k - 2] - z);

            // Make multipliers for y from i == [0, k-3]
            let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
                let (_, _, o) = cs.multiply(prev_out.into(), y[i] - z);
                o
            });

            // Constrain last x mul output and last y mul output to be equal
            cs.constrain(first_mulx_out - first_muly_out);

            Ok(())
        })
    }
}

impl ShuffleProof {
    /// Attempt to construct a proof that `output` is a permutation of `input`.
    ///
    /// Returns a tuple `(proof, input_commitments || output_commitments)`.
    pub fn prove(
        pc_gens: &PedersenGens,
        bp_gens: &BulletproofGens,
        transcript: &mut Transcript,
        input: &[Scalar],
        output: &[Scalar],
    ) -> Result<(ShuffleProof, Vec<StarkPoint>, Vec<StarkPoint>), R1CSError> {
        // Apply a domain separator with the shuffle parameters to the transcript
        // XXX should this be part of the gadget?
        let mut rng = thread_rng();
        let k = input.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_u64(b"k", k as u64);

        let mut prover = Prover::new(pc_gens, transcript);
        let (input_commitments, input_vars): (Vec<_>, Vec<_>) = input
            .iter()
            .map(|v| prover.commit(*v, Scalar::random(&mut rng)))
            .unzip();

        let (output_commitments, output_vars): (Vec<_>, Vec<_>) = output
            .iter()
            .map(|v| prover.commit(*v, Scalar::random(&mut rng)))
            .unzip();

        ShuffleProof::gadget(&mut prover, input_vars, output_vars)?;

        let proof = prover.prove(bp_gens)?;

        Ok((ShuffleProof(proof), input_commitments, output_commitments))
    }
}

impl ShuffleProof {
    /// Attempt to verify a `ShuffleProof`.
    pub fn verify(
        &self,
        pc_gens: &PedersenGens,
        bp_gens: &BulletproofGens,
        transcript: &mut Transcript,
        input_commitments: &[StarkPoint],
        output_commitments: &[StarkPoint],
    ) -> Result<(), R1CSError> {
        // Apply a domain separator with the shuffle parameters to the transcript
        // XXX should this be part of the gadget?
        let k = input_commitments.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_u64(b"k", k as u64);

        let mut verifier = Verifier::new(pc_gens, transcript);

        let input_vars: Vec<_> = input_commitments
            .iter()
            .map(|V| verifier.commit(*V))
            .collect();

        let output_vars: Vec<_> = output_commitments
            .iter()
            .map(|V| verifier.commit(*V))
            .collect();

        ShuffleProof::gadget(&mut verifier, input_vars, output_vars)?;

        verifier.verify(&self.0, bp_gens)
    }
}

fn kshuffle_helper(k: usize) {
    use rand::Rng;

    // Common code
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new((2 * k).next_power_of_two(), 1);

    let (proof, input_commitments, output_commitments) = {
        // Randomly generate inputs and outputs to kshuffle
        let mut rng = rand::thread_rng();
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<Scalar> = (0..k)
            .map(|_| Scalar::from(rng.gen_range(min..max)))
            .collect();
        let mut output = input.clone();
        output.shuffle(&mut rand::thread_rng());

        let mut prover_transcript = Transcript::new(b"ShuffleProofTest");
        ShuffleProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, &input, &output).unwrap()
    };

    {
        let mut verifier_transcript = Transcript::new(b"ShuffleProofTest");
        assert!(proof
            .verify(
                &pc_gens,
                &bp_gens,
                &mut verifier_transcript,
                &input_commitments,
                &output_commitments
            )
            .is_ok());
    }
}

#[test]
fn shuffle_gadget_test_1() {
    kshuffle_helper(1);
}

#[test]
fn shuffle_gadget_test_2() {
    kshuffle_helper(2);
}

#[test]
fn shuffle_gadget_test_3() {
    kshuffle_helper(3);
}

#[test]
fn shuffle_gadget_test_4() {
    kshuffle_helper(4);
}

#[test]
fn shuffle_gadget_test_5() {
    kshuffle_helper(5);
}

#[test]
fn shuffle_gadget_test_6() {
    kshuffle_helper(6);
}

#[test]
fn shuffle_gadget_test_7() {
    kshuffle_helper(7);
}

#[test]
fn shuffle_gadget_test_24() {
    kshuffle_helper(24);
}

#[test]
fn shuffle_gadget_test_42() {
    kshuffle_helper(42);
}

/// Constrains (a1 + a2) * (b1 + b2) = (c1 + c2)
fn example_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    a1: LinearCombination,
    a2: LinearCombination,
    b1: LinearCombination,
    b2: LinearCombination,
    c1: LinearCombination,
    c2: LinearCombination,
) {
    let (_, _, c_var) = cs.multiply(a1 + a2, b1 + b2);
    cs.constrain(c1 + c2 - c_var);
}

// Prover's scope
#[allow(clippy::too_many_arguments)]
fn example_gadget_proof(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> Result<(R1CSProof, Vec<StarkPoint>), R1CSError> {
    let mut rng = thread_rng();
    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    // 1. Create a prover
    let mut prover = Prover::new(pc_gens, &mut transcript);

    // 2. Commit high-level variables
    let (commitments, vars): (Vec<_>, Vec<_>) = [a1, a2, b1, b2, c1]
        .into_iter()
        .map(|x| prover.commit(Scalar::from(x), Scalar::random(&mut rng)))
        .unzip();

    // 3. Build a CS
    example_gadget(
        &mut prover,
        vars[0].into(),
        vars[1].into(),
        vars[2].into(),
        vars[3].into(),
        vars[4].into(),
        Scalar::from(c2).into(),
    );

    // 4. Make a proof
    let proof = prover.prove(bp_gens)?;

    Ok((proof, commitments))
}

// Verifier logic
fn example_gadget_verify(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    c2: u64,
    proof: R1CSProof,
    commitments: Vec<StarkPoint>,
) -> Result<(), R1CSError> {
    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    // 1. Create a verifier
    let mut verifier = Verifier::new(pc_gens, &mut transcript);

    // 2. Commit high-level variables
    let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();

    // 3. Build a CS
    example_gadget(
        &mut verifier,
        vars[0].into(),
        vars[1].into(),
        vars[2].into(),
        vars[3].into(),
        vars[4].into(),
        Scalar::from(c2).into(),
    );

    // 4. Verify the proof
    verifier
        .verify(&proof, bp_gens)
        .map_err(|_| R1CSError::VerificationError)
}

fn example_gadget_roundtrip_helper(
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let (proof, commitments) = example_gadget_proof(&pc_gens, &bp_gens, a1, a2, b1, b2, c1, c2)?;

    example_gadget_verify(&pc_gens, &bp_gens, c2, proof, commitments)
}

fn example_gadget_roundtrip_serialization_helper(
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let (proof, commitments) = example_gadget_proof(&pc_gens, &bp_gens, a1, a2, b1, b2, c1, c2)?;

    let proof = proof.to_bytes();

    let proof = R1CSProof::from_bytes(&proof)?;

    example_gadget_verify(&pc_gens, &bp_gens, c2, proof, commitments)
}

// Extract weight matrix for example gadget from prover
fn example_gadget_constraint_ir_prover(
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> CircuitWeights {
    // Common
    let mut rng = thread_rng();
    let pc_gens = PedersenGens::default();

    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    // 1. Create a prover
    let mut prover = Prover::new(&pc_gens, &mut transcript);

    // 2. Commit high-level variables
    let (_, vars): (Vec<_>, Vec<_>) = [a1, a2, b1, b2, c1]
        .into_iter()
        .map(|x| prover.commit(Scalar::from(x), Scalar::random(&mut rng)))
        .unzip();

    // 3. Build a CS
    example_gadget(
        &mut prover,
        vars[0].into(),
        vars[1].into(),
        vars[2].into(),
        vars[3].into(),
        vars[4].into(),
        Scalar::from(c2).into(),
    );

    // 4. Extract weight matrices from CS
    prover.get_weights()
}

// Extract weight matrix for example gadget from verifier
fn example_gadget_constraint_ir_verifier(
    a1: u64,
    a2: u64,
    b1: u64,
    b2: u64,
    c1: u64,
    c2: u64,
) -> CircuitWeights {
    // Common
    let mut rng = thread_rng();
    let pc_gens = PedersenGens::default();

    let mut transcript = Transcript::new(b"R1CSExampleGadget");

    let commitments: Vec<StarkPoint>;
    {
        // Open new scope so that we can reuse `&mut transcript`,
        // it's fine to drop prover after we generate commitments

        // 1. Create a prover to generate commitments
        let mut prover = Prover::new(&pc_gens, &mut transcript);

        // 2. Commit high-level variables (prover)
        let (prover_commitments, _): (Vec<_>, Vec<_>) = [a1, a2, b1, b2, c1]
            .into_iter()
            .map(|x| prover.commit(Scalar::from(x), Scalar::random(&mut rng)))
            .unzip();

        commitments = prover_commitments;
    }

    // 3. Create a verifier
    let mut verifier = Verifier::new(&pc_gens, &mut transcript);

    // 4. Commit high-level variables (verifier)
    let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();

    // 5. Build a CS
    example_gadget(
        &mut verifier,
        vars[0].into(),
        vars[1].into(),
        vars[2].into(),
        vars[3].into(),
        vars[4].into(),
        Scalar::from(c2).into(),
    );

    // 6. Extract weight matrices from CS
    verifier.get_weights()
}

lazy_static! {
    static ref EXAMPLE_GADGET_A1: u64 = 3;
    static ref EXAMPLE_GADGET_A2: u64 = 4;
    static ref EXAMPLE_GADGET_B1: u64 = 6;
    static ref EXAMPLE_GADGET_B2: u64 = 1;
    static ref EXAMPLE_GADGET_C1: u64 = 40;
    static ref EXAMPLE_GADGET_C2: u64 = 9;

    /*
    Constraints are represented by the following matrix equation:

    w_L * a_L + w_R * a_R + w_O * a_O = w_V * v + c

    where w_{i} are weight matrices, a_{i} are multiplier gate variable vectors,
    v is the vector of high-level witness variables, and c is the vector of constants.

    The example gadget constrains:

    (a1 + a2) * (b1 + b2) = (c1 + c2)

    Where a1, a2, b1, b2, & c1 are high-level witness variables,
    and c2 is a public constant.

    Under the hood of the example gadget, we do more or less the following:
    ```
        v[0] = a1
        v[1] = a2
        v[2] = b1
        v[3] = b2
        v[4] = c1

        a3 = eval(v[0] + v[1])
        a_L[0] = a3
        constraints[0] = (v[0] + v[1]) - a_L[0]

        b3 = eval(v[2] + v[3])
        a_R[0] = b3
        constraints[1] = (v[2] + v[3]) - a_R[0]

        o = a3 * b3
        a_O[0] = o

        constraints[2] = (v[4] + c2) - a_O[0]
    ```

    Thus, matrices (& c vector) representing this gadget should be:
    ```
        Original matrix:                Sparse-reduced matrix:

        w_L = [                         [
            [-1],                          [(0, -1)]
            [0],                           []
            [0],                           []
        ]                               ]

        w_R = [                         [
            [0],                           []
            [-1],                          [(0, -1)]
            [0],                           []
        ]                               ]

        w_O = [                         [
            [0],                           []
            [0],                           []
            [-1],                          [(0, -1)]
        ]                               ]

        Weights here are negative b/c on RHS of matrix equation
        w_V = [                         [
            [-1, -1, 0, 0, 0],             [(0, -1), (1, -1)]
            [0, 0, -1, -1, 0],             [(2, -1), (3, -1)]
            [0, 0, 0, 0, -1],              [(4, -1)]
        ]                               ]

        Weights here are negative b/c on RHS of matrix equation
        c = [
            0,
            0,                          [(2, -c2)]
            -c2,
        ]
    */

    static ref EXAMPLE_GADGET_WEIGHTS: CircuitWeights = CircuitWeights {
        w_l: SparseReducedMatrix(vec![
            SparseWeightRow(vec![(0, -Scalar::one())]),
            SparseWeightRow(vec![]),
            SparseWeightRow(vec![]),
        ]),
        w_r: SparseReducedMatrix(vec![
            SparseWeightRow(vec![]),
            SparseWeightRow(vec![(0, -Scalar::one())]),
            SparseWeightRow(vec![]),
        ]),
        w_o: SparseReducedMatrix(vec![
            SparseWeightRow(vec![]),
            SparseWeightRow(vec![]),
            SparseWeightRow(vec![(0, -Scalar::one())]),
        ]),
        w_v: SparseReducedMatrix(vec![
            SparseWeightRow(vec![(0, -Scalar::one()), (1, -Scalar::one())]),
            SparseWeightRow(vec![(2, -Scalar::one()), (3, -Scalar::one())]),
            SparseWeightRow(vec![(4, -Scalar::one())]),
        ]),
        c: SparseWeightRow(vec![(2, -Scalar::from(*EXAMPLE_GADGET_C2))])
    };
}

#[test]
fn example_gadget_test() {
    // (3 + 4) * (6 + 1) = (40 + 9)
    assert!(example_gadget_roundtrip_helper(
        *EXAMPLE_GADGET_A1,
        *EXAMPLE_GADGET_A2,
        *EXAMPLE_GADGET_B1,
        *EXAMPLE_GADGET_B2,
        *EXAMPLE_GADGET_C1,
        *EXAMPLE_GADGET_C2
    )
    .is_ok());
    // (3 + 4) * (6 + 1) != (40 + 10)
    assert!(example_gadget_roundtrip_helper(
        *EXAMPLE_GADGET_A1,
        *EXAMPLE_GADGET_A2,
        *EXAMPLE_GADGET_B1,
        *EXAMPLE_GADGET_B2,
        *EXAMPLE_GADGET_C1,
        10
    )
    .is_err());
}

#[test]
fn example_gadget_serialization_test() {
    // (3 + 4) * (6 + 1) = (40 + 9)
    assert!(example_gadget_roundtrip_serialization_helper(
        *EXAMPLE_GADGET_A1,
        *EXAMPLE_GADGET_A2,
        *EXAMPLE_GADGET_B1,
        *EXAMPLE_GADGET_B2,
        *EXAMPLE_GADGET_C1,
        *EXAMPLE_GADGET_C2
    )
    .is_ok());
    // (3 + 4) * (6 + 1) != (40 + 10)
    assert!(example_gadget_roundtrip_serialization_helper(
        *EXAMPLE_GADGET_A1,
        *EXAMPLE_GADGET_A2,
        *EXAMPLE_GADGET_B1,
        *EXAMPLE_GADGET_B2,
        *EXAMPLE_GADGET_C1,
        10
    )
    .is_err());
}

#[test]
fn example_gadget_constraint_ir_prover_test() {
    let circuit_weights = example_gadget_constraint_ir_prover(
        *EXAMPLE_GADGET_A1,
        *EXAMPLE_GADGET_A2,
        *EXAMPLE_GADGET_B1,
        *EXAMPLE_GADGET_B2,
        *EXAMPLE_GADGET_C1,
        *EXAMPLE_GADGET_C2,
    );

    assert!(circuit_weights == *EXAMPLE_GADGET_WEIGHTS);
}

#[test]
fn example_gadget_constraint_ir_verifier_test() {
    let circuit_weights = example_gadget_constraint_ir_verifier(
        *EXAMPLE_GADGET_A1,
        *EXAMPLE_GADGET_A2,
        *EXAMPLE_GADGET_B1,
        *EXAMPLE_GADGET_B2,
        *EXAMPLE_GADGET_C1,
        *EXAMPLE_GADGET_C2,
    );

    assert!(circuit_weights == *EXAMPLE_GADGET_WEIGHTS);
}

// Range Proof gadget

/// Enforces that the quantity of v is in the range [0, 2^n).
pub fn range_proof<CS: ConstraintSystem>(
    cs: &mut CS,
    mut v: LinearCombination,
    v_assignment: Option<u64>,
    n: usize,
) -> Result<(), R1CSError> {
    let mut exp_2 = Scalar::one();
    for i in 0..n {
        // Create low-level variables and add them to constraints
        let (a, b, o) = cs.allocate_multiplier(v_assignment.map(|q| {
            let bit: u64 = (q >> i) & 1;
            ((1 - bit).into(), bit.into())
        }))?;

        // Enforce a * b = 0, so one of (a,b) is zero
        cs.constrain(o.into());

        // Enforce that a = 1 - b, so they both are 1 or 0.
        cs.constrain(a + (b - 1u64));

        // Add `-b_i*2^i` to the linear combination
        // in order to form the following constraint by the end of the loop:
        // v = Sum(b_i * 2^i, i = 0..n-1)
        v -= b * exp_2;

        exp_2 = exp_2 + exp_2;
    }

    // Enforce that v = Sum(b_i * 2^i, i = 0..n-1)
    cs.constrain(v);

    Ok(())
}

#[test]
fn range_proof_gadget() {
    use rand::thread_rng;
    use rand::Rng;

    let mut rng = thread_rng();
    let m = 3; // number of values to test per `n`

    for n in [2, 10, 32, 63].iter() {
        let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
        let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min..max)).collect();
        for v in values {
            assert!(range_proof_helper(v, *n).is_ok());
        }
        assert!(range_proof_helper(max + 1, *n).is_err());
    }
}

fn range_proof_helper(v_val: u64, n: usize) -> Result<(), R1CSError> {
    // Common
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    // Prover's scope
    let (proof, commitment) = {
        // Prover makes a `ConstraintSystem` instance representing a range proof gadget
        let mut prover_transcript = Transcript::new(b"RangeProofTest");

        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let (com, var) = prover.commit(v_val.into(), Scalar::random(&mut thread_rng()));
        assert!(range_proof(&mut prover, var.into(), Some(v_val), n).is_ok());

        let proof = prover.prove(&bp_gens)?;

        (proof, com)
    };

    // Verifier makes a `ConstraintSystem` instance representing a merge gadget
    let mut verifier_transcript = Transcript::new(b"RangeProofTest");
    let mut verifier = Verifier::new(&pc_gens, &mut verifier_transcript);

    let var = verifier.commit(commitment);

    // Verifier adds constraints to the constraint system
    assert!(range_proof(&mut verifier, var.into(), None, n).is_ok());

    // Verifier verifies proof
    verifier.verify(&proof, &bp_gens)
}
