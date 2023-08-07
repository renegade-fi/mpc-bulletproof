//! Groups definitions for the MPC prover

use core::{borrow::BorrowMut, iter};

use crate::{
    errors::{MultiproverError, R1CSError},
    r1cs::Variable,
    transcript::MpcTranscript,
    util, BulletproofGens, PedersenGens,
};
use futures_util::future::join_all;
use itertools::Itertools;
use merlin::HashChainTranscript as Transcript;
use mpc_stark::{
    algebra::{
        authenticated_scalar::AuthenticatedScalarResult,
        authenticated_stark_point::{
            AuthenticatedStarkPointOpenResult, AuthenticatedStarkPointResult,
        },
        scalar::{Scalar, ScalarResult},
        stark_curve::StarkPoint,
    },
    beaver::SharedValueSource,
    error::MpcError,
    network::{PartyId, QuicTwoPartyNet},
    MpcFabric,
};

use super::{
    authenticated_poly::{AuthenticatedPoly6, AuthenticatedVecPoly3},
    mpc_constraint_system::{
        MpcConstraintSystem, MpcRandomizableConstraintSystem, MpcRandomizedConstraintSystem,
    },
    mpc_inner_product::SharedInnerProductProof,
    mpc_linear_combination::{MpcLinearCombination, MpcVariable},
    PartiallySharedR1CSProof,
};

/// An implementation of a collaborative Bulletproof prover.
///
/// This prover represents one peer in an MPC network. Together
/// with one (or more) peers, it generates a proof of knowledge
/// of satisfying witness for a given R1CS relation.
///
/// This Bulletproof R1CS implementation has two types of constraints:
///     1. Multiplicative constraints of the form a_l * a_r = a_o, these
///        are encoded in the respective vectors
///     2. A system of linear constraints of the form:
///          W_l * a_l + W_r * a_r + W_o * a_o = W_v * v + c
///       where W_l, W_r, W_o, W_v are the respective vectors of weights, and
///       are typically very sparse. These are represented in the constraints
///       field, which is a sparse representation of the weight matrices.
///
/// As well, Bulletproofs allow for constraints to be added "on the fly" during the proving process.
/// These constraints are called "randomized constraints" as they have access to random Fiat-Shamir
/// challenges from the protocol transcript that precedes them. These constraints are encoded in the
/// `deferred_constraints` field.
#[allow(dead_code, non_snake_case)]
pub struct MpcProver<'a, 't, 'g> {
    /// The protocol transcript, used for constructing Fiat-Shamir challenges
    transcript: MpcTranscript,
    /// Generators used for Pedersen commitments
    pc_gens: &'g PedersenGens,
    /// Teh constraints accumulated so far.
    constraints: Vec<MpcLinearCombination>,
    /// Stores assignments to the "left" of multiplication gates.
    a_L: Vec<AuthenticatedScalarResult>,
    /// Stores assignments to the "right" of multiplication gates.
    a_R: Vec<AuthenticatedScalarResult>,
    /// Stores assignments to the "output" of multiplication gates.
    a_O: Vec<AuthenticatedScalarResult>,
    /// High-level witness assignments (value openings to V commitments)
    /// where we use a pedersen commitment `value * G + blinding * H`
    v: Vec<AuthenticatedScalarResult>,
    /// High-level public variables that are allocated in hte constraint system
    v_public: Vec<ScalarResult>,
    /// High level witness data (blinding openings to V commitments)
    v_blinding: Vec<AuthenticatedScalarResult>,
    /// Index of a pending multiplier that hasn't been assigned yet
    pending_multiplier: Option<usize>,
    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    #[allow(clippy::type_complexity)]
    deferred_constraints:
        Vec<Box<dyn Fn(&mut RandomizingMpcProver<'a, 't, 'g>) -> Result<(), R1CSError> + 'a>>,
    /// The underlying MPC fabric
    fabric: MpcFabric,
}

/// A prover in the randomizing phase.
///
/// In this phase constraints may be built using challenge scalars derived from the
/// protocol transcript so far.
pub struct RandomizingMpcProver<'a, 't, 'g> {
    prover: MpcProver<'a, 't, 'g>,
}

impl<'a, 't, 'g> MpcProver<'a, 't, 'g> {
    /// Create a new MpcProver with a custom network
    pub fn new_with_network<S: 'static + SharedValueSource>(
        network: QuicTwoPartyNet,
        beaver_source: S,
        transcript: Transcript,
        pc_gens: &'g PedersenGens,
    ) -> Self {
        // Build a fabric and transcript
        let fabric = MpcFabric::new(network, beaver_source);
        let mut transcript = MpcTranscript::new(transcript, fabric.clone());

        // Record the beginning of the r1cs protocol
        transcript.r1cs_domain_sep();

        Self {
            transcript,
            pc_gens,
            fabric,
            constraints: Vec::new(),
            a_L: Vec::new(),
            a_R: Vec::new(),
            a_O: Vec::new(),
            v: Vec::new(),
            v_public: Vec::new(),
            v_blinding: Vec::new(),
            deferred_constraints: Vec::new(),
            pending_multiplier: None,
        }
    }

    /// Create a new MpcProver with a given MPC fabric already allocated
    pub fn new_with_fabric(
        fabric: MpcFabric,
        transcript: Transcript,
        pc_gens: &'g PedersenGens,
    ) -> Self {
        let mut transcript = MpcTranscript::new(transcript, fabric.clone());
        transcript.r1cs_domain_sep();

        Self {
            transcript,
            pc_gens,
            fabric,
            constraints: Vec::new(),
            a_L: Vec::new(),
            a_R: Vec::new(),
            a_O: Vec::new(),
            v: Vec::new(),
            v_public: Vec::new(),
            v_blinding: Vec::new(),
            deferred_constraints: Vec::new(),
            pending_multiplier: None,
        }
    }

    /// Fetch the number of constraints currently registered in the prover
    ///
    /// Used as a profiling metric
    #[cfg(feature = "benchmarking")]
    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    /// Fetch the number of multiplication gates registered in the prover
    ///
    /// Used as a profiling metric
    #[cfg(feature = "benchmarking")]
    pub fn num_multipliers(&self) -> usize {
        self.a_O.len()
    }

    /// Get the party ID of the local party in the MPC network
    pub fn party_id(&self) -> u64 {
        self.fabric.party_id()
    }
}

impl<'a, 't, 'g> MpcConstraintSystem<'a> for MpcProver<'a, 't, 'g> {
    /// Lease the transcript to the caller
    fn transcript(&mut self) -> &mut MpcTranscript {
        self.transcript.borrow_mut()
    }

    #[allow(unused_variables)]
    fn multiply(
        &mut self,
        left: &MpcLinearCombination,
        right: &MpcLinearCombination,
    ) -> Result<(MpcVariable, MpcVariable, MpcVariable), MultiproverError> {
        let l = self.eval(left);
        let r = self.eval(right);
        let o = &l * &r;

        // Create new variables for the results
        let l_var = MpcVariable::new_with_type(
            Variable::MultiplierLeft(self.a_L.len()),
            self.fabric.clone(),
        );
        let r_var = MpcVariable::new_with_type(
            Variable::MultiplierRight(self.a_R.len()),
            self.fabric.clone(),
        );
        let o_var = MpcVariable::new_with_type(
            Variable::MultiplierOutput(self.a_O.len()),
            self.fabric.clone(),
        );

        // Add the value assignments
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        // Constrain the multiplication
        let mut left_constraints = left.clone();
        left_constraints.add_term(l_var.clone(), -self.fabric.allocate_scalar(1));
        let mut right_constraints = right.clone();
        right_constraints.add_term(r_var.clone(), -self.fabric.allocate_scalar(1));
        self.constrain(left_constraints);
        self.constrain(right_constraints);

        Ok((l_var, r_var, o_var))
    }

    fn allocate(
        &mut self,
        assignment: Option<AuthenticatedScalarResult>,
    ) -> Result<MpcVariable, R1CSError> {
        // Allocate a scalar in the MPC network, assume public visibility
        let scalar = assignment.ok_or(R1CSError::MissingAssignment)?;

        // If there is a pending multiplier, allocate this scalar as the right
        // hand side of the multiplication gate
        match self.pending_multiplier {
            None => {
                let i = self.a_L.len();
                self.pending_multiplier = Some(i);
                self.a_L.push(scalar);
                let allocated_zero = self.fabric.zero_authenticated();
                self.a_R.push(allocated_zero.clone());
                self.a_O.push(allocated_zero);
                Ok(MpcVariable::new_with_type(
                    Variable::MultiplierLeft(i),
                    self.fabric.clone(),
                ))
            }
            Some(i) => {
                self.pending_multiplier = None;
                self.a_R[i] = scalar;
                self.a_O[i] = &self.a_L[i] * &self.a_R[i];
                Ok(MpcVariable::new_with_type(
                    Variable::MultiplierRight(i),
                    self.fabric.clone(),
                ))
            }
        }
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(AuthenticatedScalarResult, AuthenticatedScalarResult)>,
    ) -> Result<(MpcVariable, MpcVariable, MpcVariable), R1CSError> {
        // Allocate a scalar in the MPC network, assume public visibility
        let (left, right) = input_assignments.ok_or(R1CSError::MissingAssignment)?;

        // Allocate the output of the multiplication gate
        self.a_O.push(&left * &right);
        self.a_L.push(left);
        self.a_R.push(right);

        Ok((
            MpcVariable::new_with_type(
                Variable::MultiplierLeft(self.a_L.len() - 1),
                self.fabric.clone(),
            ),
            MpcVariable::new_with_type(
                Variable::MultiplierRight(self.a_R.len() - 1),
                self.fabric.clone(),
            ),
            MpcVariable::new_with_type(
                Variable::MultiplierOutput(self.a_O.len() - 1),
                self.fabric.clone(),
            ),
        ))
    }

    fn multipliers_len(&self) -> usize {
        self.a_L.len()
    }

    fn constrain(&mut self, lc: MpcLinearCombination) {
        self.constraints.push(lc)
    }

    /// Evaluate a linear combination of allocated variables
    fn eval(&self, lc: &MpcLinearCombination) -> AuthenticatedScalarResult {
        self.eval_lc(lc)
    }
}

impl<'a, 't, 'g> MpcRandomizableConstraintSystem<'a> for MpcProver<'a, 't, 'g> {
    type RandomizedCS = RandomizingMpcProver<'a, 't, 'g>;

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        F: 'a + Fn(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        self.deferred_constraints.push(Box::new(callback));
        Ok(())
    }
}

impl<'a, 't, 'g> MpcConstraintSystem<'a> for RandomizingMpcProver<'a, 't, 'g> {
    fn transcript(&mut self) -> &mut MpcTranscript {
        self.prover.transcript()
    }

    fn multiply(
        &mut self,
        left: &MpcLinearCombination,
        right: &MpcLinearCombination,
    ) -> Result<(MpcVariable, MpcVariable, MpcVariable), MultiproverError> {
        self.prover.multiply(left, right)
    }

    fn allocate(
        &mut self,
        assignment: Option<AuthenticatedScalarResult>,
    ) -> Result<MpcVariable, R1CSError> {
        self.prover.allocate(assignment)
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(AuthenticatedScalarResult, AuthenticatedScalarResult)>,
    ) -> Result<(MpcVariable, MpcVariable, MpcVariable), R1CSError> {
        self.prover.allocate_multiplier(input_assignments)
    }

    fn multipliers_len(&self) -> usize {
        self.prover.multipliers_len()
    }

    fn constrain(&mut self, lc: MpcLinearCombination) {
        self.prover.constrain(lc)
    }

    fn eval(&self, lc: &MpcLinearCombination) -> AuthenticatedScalarResult {
        self.prover.eval(lc)
    }
}

impl<'a, 't, 'g> MpcRandomizedConstraintSystem<'a> for RandomizingMpcProver<'a, 't, 'g> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> ScalarResult {
        self.prover.transcript.challenge_scalar(label)
    }
}

impl<'a, 't, 'g> MpcProver<'a, 't, 'g> {
    /// From a privately held input value, secret share the value and commit to it
    ///
    /// The result is a variable allocated both in the MPC network and in the
    /// constraint system; along with its respectively commitment.
    #[allow(clippy::type_complexity)]
    pub fn commit<T: Into<Scalar>>(
        &mut self,
        owning_party: PartyId,
        v: T,
        v_blinding: Scalar,
    ) -> Result<(AuthenticatedStarkPointOpenResult, MpcVariable), MpcError> {
        // Allocate the value in the MPC network and then commit to the shared value
        let shared_v = self.fabric.share_scalar(v, owning_party);
        let shared_blinder = self.fabric.allocate_preshared_scalar(v_blinding);
        self.commit_preshared(&shared_v, &shared_blinder)
    }

    /// Commit to a batch of values
    pub fn batch_commit<I, T>(
        &mut self,
        owning_party: PartyId,
        v: I,
        v_blinding: &[Scalar],
    ) -> Result<(Vec<AuthenticatedStarkPointOpenResult>, Vec<MpcVariable>), MpcError>
    where
        I: IntoIterator<Item = T>,
        T: Into<Scalar>,
    {
        let v = v.into_iter().map(Into::into).collect_vec();
        assert_eq!(v.len(), v_blinding.len());

        // Share scalars with counterparty
        let shared_v = self.fabric.batch_share_scalar(v, owning_party);
        let shared_blinder = self
            .fabric
            .batch_allocate_preshared_scalar(v_blinding.to_vec());

        self.batch_commit_preshared(&shared_v, &shared_blinder)
    }

    /// Commit to a pre-shared value
    ///
    /// This assumes that parties call this method with their respective secret shares of the underlying
    /// committed input.
    #[allow(clippy::type_complexity)]
    pub fn commit_preshared(
        &mut self,
        v: &AuthenticatedScalarResult,
        v_blinding: &AuthenticatedScalarResult,
    ) -> Result<(AuthenticatedStarkPointOpenResult, MpcVariable), MpcError> {
        // Commit to the input, open the commitment, and add the commitment to the transcript.
        let value_commit = self
            .pc_gens
            .commit_shared(v, v_blinding)
            .open_authenticated();
        self.transcript.append_point(b"V", &value_commit.value);

        // Add the value to the constraint system
        let i = self.v.len();
        self.v.push(v.clone());
        self.v_blinding.push(v_blinding.clone());

        Ok((
            value_commit,
            MpcVariable::new_with_type(Variable::Committed(i), self.fabric.clone()),
        ))
    }

    /// Commit to a batch of pre-shared values
    pub fn batch_commit_preshared(
        &mut self,
        v: &[AuthenticatedScalarResult],
        v_blinding: &[AuthenticatedScalarResult],
    ) -> Result<(Vec<AuthenticatedStarkPointOpenResult>, Vec<MpcVariable>), MpcError> {
        assert_eq!(v.len(), v_blinding.len());
        let n = v.len();

        // Open the blinders
        let commitments = v
            .iter()
            .zip(v_blinding.iter())
            .map(|(value, blinder)| self.pc_gens.commit_shared(value, blinder))
            .collect_vec();
        let open_comms = AuthenticatedStarkPointResult::open_authenticated_batch(&commitments);

        open_comms
            .iter()
            .for_each(|blinder| self.transcript.append_point(b"V", &blinder.value));

        let i = self.v.len();
        self.v.append(&mut v.to_vec());
        self.v_blinding.append(&mut v_blinding.to_vec());

        Ok((
            open_comms,
            (i..i + n)
                .map(|i| MpcVariable::new_with_type(Variable::Committed(i), self.fabric.clone()))
                .collect(),
        ))
    }

    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    #[allow(non_snake_case, clippy::type_complexity)]
    fn flattened_constraints(
        &mut self,
        z: &ScalarResult,
    ) -> (
        Vec<AuthenticatedScalarResult>,
        Vec<AuthenticatedScalarResult>,
        Vec<AuthenticatedScalarResult>,
        Vec<AuthenticatedScalarResult>,
    ) {
        let n = self.a_L.len();
        let m = self.v.len();

        let mut wL = self.fabric.zeros_authenticated(n);
        let mut wR = self.fabric.zeros_authenticated(n);
        let mut wO = self.fabric.zeros_authenticated(n);
        let mut wV = self.fabric.zeros_authenticated(m);

        let mut exp_z = z.clone();
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var.get_type() {
                    Variable::MultiplierLeft(i) => {
                        wL[i] = &wL[i] + &exp_z * coeff;
                    }
                    Variable::MultiplierRight(i) => {
                        wR[i] = &wR[i] + &exp_z * coeff;
                    }
                    Variable::MultiplierOutput(i) => {
                        wO[i] = &wO[i] + &exp_z * coeff;
                    }
                    Variable::Committed(i) => {
                        wV[i] = &wV[i] - &exp_z * coeff;
                    }
                    Variable::One() | Variable::Zero() => {
                        // The prover doesn't need to handle constant terms
                    }
                }
            }
            exp_z = exp_z * z;
        }

        (wL, wR, wO, wV)
    }

    // Calls the callbacks that allocate randomized constraints
    // Theses are stored in the `deferred_constraints` field
    fn create_randomized_constraints(mut self) -> Result<Self, R1CSError> {
        // Clear the pending multiplier (if any) because it was committed into A_L/A_R/S.
        self.pending_multiplier = None;

        if self.deferred_constraints.is_empty() {
            self.transcript.r1cs_1phase_domain_sep();
            Ok(self)
        } else {
            self.transcript.r1cs_2phase_domain_sep();
            // Note: the wrapper could've used &mut instead of ownership,
            // but specifying lifetimes for boxed closures is not going to be nice,
            // so we move the self into wrapper and then move it back out afterwards.
            let mut callbacks = std::mem::take(&mut self.deferred_constraints);
            let mut wrapped_self = RandomizingMpcProver { prover: self };
            for callback in callbacks.drain(..) {
                callback(&mut wrapped_self)?;
            }
            Ok(wrapped_self.prover)
        }
    }

    /// Evaluate a linear combination of allocated variables
    pub fn eval_lc(&self, lc: &MpcLinearCombination) -> AuthenticatedScalarResult {
        let mut sum = self.fabric.zero_authenticated();
        for (var, coeff) in lc.terms.iter() {
            let resolved_val = match var.get_type() {
                Variable::MultiplierLeft(i) => self.a_L[i].to_owned(),
                Variable::MultiplierRight(i) => self.a_R[i].to_owned(),
                Variable::MultiplierOutput(i) => self.a_O[i].to_owned(),
                Variable::Committed(i) => self.v[i].to_owned(),
                Variable::One() => self.fabric.one_authenticated(),
                Variable::Zero() => self.fabric.zero_authenticated(),
            };
            sum = sum + coeff * resolved_val;
        }

        sum
    }

    /// Checks whether all the constraints are satisfied, does not prove the statement
    pub async fn constraints_satisfied(&self) -> bool {
        let mut evals = Vec::with_capacity(self.constraints.len());
        for constraint in self.constraints.iter() {
            evals.push(self.eval_lc(constraint));
        }

        // Check that all the constraints are satisfied
        let open_results = AuthenticatedScalarResult::open_batch(&evals);
        join_all(open_results)
            .await
            .into_iter()
            .all(|res| res == Scalar::zero())
    }

    /// Consume this `ConstraintSystem` and produce a shared proof
    /// TODO: Remove these clippy allowances
    ///
    /// Throughout proof generation we open intermediate proof results that go into
    /// the transcript. This is in order to keep the transcripts of the provers in sync
    /// as they derive Fiat-Shamir challenges from these transcripts. This is simpler
    /// than deriving the challenges in secret sharing space as we would have to hash
    /// within the MPC circuit, and implement a hasher on top of the authenticated field.
    #[allow(non_snake_case)]
    pub fn prove(
        mut self,
        bp_gens: &BulletproofGens,
    ) -> Result<PartiallySharedR1CSProof, MultiproverError> {
        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.transcript.append_u64(b"m", self.v.len() as u64);

        // Commit to the low-level witness data, a_l, a_r, a_o in the multiplication
        // gates.
        // Both parties use the same generator chain here. We do this to avoid communication
        // overhead; as a multiscalar mul with a public generator chain will not induce
        // communication, all Pedersen commitments can be computed locally.
        let gens = bp_gens.as_mpc_values();

        // Multiplicative depth of the circuit
        let n1 = self.a_L.len();

        // Allow party 0 to generate the blinding factors and distribute the shares
        // We need 2n1 + 3 blinding factors, 3 for commitments to A_I (inputs) and A_O (outputs)
        // and n1 for each of the s_L, s_R terms that are used to blind a_L and a_R directly.
        let blinding_factors = self.fabric.random_shared_scalars_authenticated(3 + 2 * n1);

        let (i_blinding1, o_blinding1, s_blinding1) = (
            blinding_factors[0].clone(),
            blinding_factors[1].clone(),
            blinding_factors[2].clone(),
        );

        let s_L1 = blinding_factors[3..3 + n1].to_vec();
        let s_R1 = blinding_factors[3 + n1..3 + 2 * n1].to_vec();

        // Allocate the Pedersen blinding generator in the network
        let B_blinding = self.pc_gens.B_blinding;

        // Construct a commitment to the multiplication gate inputs a_L and a_R
        // This commitment has the form:
        //      A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
        // where G and H are the vectors of generators for the curve group, and B_blinding
        // is the blinding Pedersen generator.
        let A_I1 = StarkPoint::msm_authenticated_iter(
            iter::once(&i_blinding1)
                .chain(self.a_L.iter())
                .chain(self.a_R.iter())
                .cloned(),
            iter::once(B_blinding)
                .chain(gens.G(n1).copied())
                .chain(gens.H(n1).copied()),
        )
        .open();

        // Construct a commitment to the multiplication gate outputs a_O
        // This commitment has the form
        //      A_O = <a_O, G> + o_blinding * B_blinding
        // where G is a vector of generators for the curve group, and B_blinding
        // is the blinding Pedersen generator.
        let A_O1 = StarkPoint::msm_authenticated_iter(
            iter::once(&o_blinding1).chain(self.a_O.iter()).cloned(),
            iter::once(B_blinding).chain(gens.G(n1).copied()),
        )
        .open();

        // Construct a commitment to the blinding factors used in the inner product proofs
        // This commitment has the form
        //    S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        // where G, H, and B_blinding are generators as above. s_L and s_R are vectors of blinding
        // factors used to hide a_L and a_R in the inner product proofs respectively.
        let S1 = StarkPoint::msm_authenticated_iter(
            iter::once(&s_blinding1)
                .chain(s_L1.iter())
                .chain(s_R1.iter())
                .cloned(),
            iter::once(B_blinding)
                .chain(gens.G(n1).copied())
                .chain(gens.H(n1).copied()),
        )
        .open();

        // Add the commitments to the transcript, these are used to generate Fiat-Shamir challenges
        self.transcript.append_point(b"A_I1", &A_I1);
        self.transcript.append_point(b"A_O1", &A_O1);
        self.transcript.append_point(b"S1", &S1);

        // Begin phase 2 of the commitments
        // In this phase, we have initialized the Fiat-Shamir transcript with the commitments
        // from phase 1. We can now specify "randomized constraints" in which the constraints
        // have access to Fiat-Shamir style challenge scalars. These constraints are specified
        // via callbacks stored in the `deferred_constraints` vector.
        // 1. Process the phase 2 constraints via their callbacks
        self = self
            .create_randomized_constraints()
            .map_err(MultiproverError::ProverError)?;

        // The range proof requires that the constraint length be a power of 2, so we pad
        let n = self.a_L.len();
        let n2 = n - n1;
        let padded_n = self.a_L.len().next_power_of_two();
        let pad = padded_n - n;

        if bp_gens.gens_capacity < padded_n {
            return Err(MultiproverError::ProverError(
                R1CSError::InvalidGeneratorsLength,
            ));
        }

        // Commit to the low-level witness data, a_l, a_r, a_o in the multiplication
        // gates from phase 2
        let has_2nd_phase_commitments = n2 > 0;

        // We once again need to allocate a series of blinding factors for the commitments
        // Here we need 3 + 2 * n2 blinding factors
        // If there are no 2nd phase commitments, zero out the blinding factors to avoid
        // unnecessarily consuming the pre-processing functionality's output
        let blinding_factors = if has_2nd_phase_commitments {
            self.fabric.random_shared_scalars_authenticated(3 + 2 * n2)
        } else {
            self.fabric.zeros_authenticated(3 + 2 * n2)
        };

        let (i_blinding2, o_blinding2, s_blinding2) = (
            blinding_factors[0].clone(),
            blinding_factors[1].clone(),
            blinding_factors[2].clone(),
        );

        let s_L2 = blinding_factors[3..3 + n2].to_vec();
        let s_R2 = blinding_factors[3 + n2..3 + 2 * n2].to_vec();

        // Commit to the second phase input, outputs, and blinding factors as above
        // If there are no second phase commitments, we can skip this and return the identity
        let (A_I2, A_O2, S2) = if has_2nd_phase_commitments {
            // Commit to the left and right inputs to the multiplication gates from phase 2
            // This commitment has the form:
            //      A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
            // where G and H are the vectors of generators for the curve group, and B_blinding
            // is the blinding Pedersen generator.
            let shared_A_I = StarkPoint::msm_authenticated_iter(
                iter::once(&i_blinding2)
                    .chain(self.a_L.iter().skip(n1))
                    .chain(self.a_R.iter().skip(n1))
                    .cloned(),
                iter::once(B_blinding)
                    .chain(gens.G(n).skip(n1).copied())
                    .chain(gens.H(n).skip(n1).copied()),
            );
            // Commit to the outputs of the multiplication gates from phase 2
            // This commitment has the form
            //      A_O = <a_O, G> + o_blinding * B_blinding
            // where G is a vector of generators for the curve group, and B_blinding
            // is the blinding Pedersen generator.
            let shared_A_O = StarkPoint::msm_authenticated_iter(
                iter::once(&o_blinding2)
                    .chain(self.a_O.iter().skip(n1))
                    .cloned(),
                iter::once(B_blinding).chain(gens.G(n).skip(n1).copied()),
            );
            // Commit to the blinding factors used in the inner product proofs
            // This commitment has the form
            //    S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
            // where G, H, and B_blinding are generators as above. s_L and s_R are vectors of blinding
            // factors used to hide a_L and a_R in the inner product proofs respectively.
            let shared_S = StarkPoint::msm_authenticated_iter(
                iter::once(&s_blinding2)
                    .chain(s_L2.iter())
                    .chain(s_R2.iter())
                    .cloned(),
                iter::once(B_blinding)
                    .chain(gens.G(n).skip(n1).copied())
                    .chain(gens.H(n).skip(n1).copied()),
            );

            // Batch open the values
            let mut opened_values =
                AuthenticatedStarkPointResult::open_batch(&[shared_A_I, shared_A_O, shared_S]);

            (
                opened_values.remove(0),
                opened_values.remove(0),
                opened_values.remove(0),
            )
        } else {
            (
                self.fabric.curve_identity(),
                self.fabric.curve_identity(),
                self.fabric.curve_identity(),
            )
        };

        // Add the commitments to the transcript
        self.transcript.append_point(b"A_I2", &A_I2);
        self.transcript.append_point(b"A_O2", &A_O2);
        self.transcript.append_point(b"S2", &S2);

        // Compute the inner product challenges y and z
        // These challenges rely on the fact that if a vector v has inner product 0 with
        // a random challenge, it is overwhelmingly likely to be the zero vector.
        // Construct these challenge vectors from increasing powers of y and z.
        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        // The assignment matrices can be flattened by pre-multiplying with their challenge vector
        let (wL, wR, wO, wV) = self.flattened_constraints(&z);

        // l_poly and r_poly form the core of the R1CS satisfaction argument, they are constructed
        // to allow us to collapse a sum of inner products into a single inner product. The value
        // we are truly proving knowledge of is encoded in the second degree monomial coefficient (t_2)
        // of <l_poly, r_poly>. We commit to the coefficients of l_poly and r_poly, and evaluate
        // the full inner product t(x) = <l(x), r(x)> at a challenge point; where the verifier
        // substitutes in the expected value for t_2
        let mut l_poly = AuthenticatedVecPoly3::zero(n, self.fabric.clone());
        let mut r_poly = AuthenticatedVecPoly3::zero(n, self.fabric.clone());

        // A sequence of challenge scalars for a_l \dot a_r - a_o
        // These challenges are public values, we can invert and construct them as plain scalars
        // and then wrap them in network allocated values.
        let mut exp_y = self.fabric.one();
        let y_inv = y.inverse();
        let exp_y_inv = util::exp_iter_result(y_inv, padded_n, &self.fabric);

        // Chain together the blinding factors for the multiplication gate inputs
        let sLsR = s_L1
            .iter()
            .chain(s_L2.iter())
            .zip(s_R1.iter().chain(s_R2.iter()));

        for (i, (sl, sr)) in sLsR.enumerate() {
            // Assign coefficients to the polynomials l_poly and r_poly
            // See https://doc-internal.dalek.rs/bulletproofs/notes/r1cs_proof/index.html#blinding-the-inner-product
            // for a derivation

            // 1st degree coefficient is: a_l + y^-n * w_r
            l_poly.1[i] = &self.a_L[i] + &exp_y_inv[i] * &wR[i];
            // 2nd degree coefficient is: a_o
            l_poly.2[i] = self.a_O[i].clone();
            // 3rd degree coefficient is: s_L
            l_poly.3[i] = sl.clone();

            // 0th degree coefficient is: w_o - y^n
            r_poly.0[i] = &wO[i] - &exp_y;
            // 1st degree coefficient is: y^n * a_r + w_l
            r_poly.1[i] = &exp_y * &self.a_R[i] + &wL[i];
            // 2nd degree coefficient is: 0
            // 3rd degree coefficient is: y^n * s_R
            r_poly.3[i] = &exp_y * sr;

            // Incrementally exponential the challenge scalar `y`
            exp_y = exp_y * &y;
        }

        // The core of the proof is two fold. Let the polynomial below be t(x) = <l(x), r(x)>; we prove:
        //      1. That the second degree coefficient of t(x) equals the public verifier input, encoding
        //         the R1CS constraint system's assignment
        //      2. An inner product proof that t(x) = <l(x), r(x)>
        let t_poly = AuthenticatedVecPoly3::special_inner_product(&l_poly, &r_poly);
        let mut t_blinding_factors = self.fabric.random_shared_scalars_authenticated(5);
        // Commit to the coefficients of t_poly using the blinding factors
        // and batch their openings
        let (T_1, T_3, T_4, T_5, T_6) = {
            let t_1_shared = self
                .pc_gens
                .commit_shared(&t_poly.t1, &t_blinding_factors[0]);
            let t_3_shared = self
                .pc_gens
                .commit_shared(&t_poly.t3, &t_blinding_factors[1]);
            let t_4_shared = self
                .pc_gens
                .commit_shared(&t_poly.t4, &t_blinding_factors[2]);
            let t_5_shared = self
                .pc_gens
                .commit_shared(&t_poly.t5, &t_blinding_factors[3]);
            let t_6_shared = self
                .pc_gens
                .commit_shared(&t_poly.t6, &t_blinding_factors[4]);

            let mut opened_values = AuthenticatedStarkPointResult::open_authenticated_batch(&[
                t_1_shared, t_3_shared, t_4_shared, t_5_shared, t_6_shared,
            ]);

            (
                opened_values.remove(0),
                opened_values.remove(0),
                opened_values.remove(0),
                opened_values.remove(0),
                opened_values.remove(0),
            )
        };

        // Add the commitments to the transcript
        self.transcript.append_point(b"T_1", &T_1.value);
        self.transcript.append_point(b"T_3", &T_3.value);
        self.transcript.append_point(b"T_4", &T_4.value);
        self.transcript.append_point(b"T_5", &T_5.value);
        self.transcript.append_point(b"T_6", &T_6.value);

        // Sample two more challenge scalars:
        //    - `u` is used to create a random linear combination of the non-randomized and randomized
        //      commitments to the polynomials l(x) and r(x). The randomized component comes from the
        //      deferred constraints, evaluated above
        //    - `x` is used to construct the challenge point `X` for the inner product proof
        let u = self.transcript.challenge_scalar(b"u");
        let x = self.transcript.challenge_scalar(b"x");

        // Because we do not commit to T_2 directly, we commit to its replacement blinding factor that
        // will satisfy the equality: https://doc-internal.dalek.rs/bulletproofs/notes/r1cs_proof/index.html#proving-that-t_2-is-correct
        let t_2_blinding: AuthenticatedScalarResult = wV
            .iter()
            .zip(self.v_blinding.iter())
            .map(|(c, v_blinding)| c * v_blinding)
            .sum();

        let t_blinding_poly = AuthenticatedPoly6 {
            t1: t_blinding_factors.remove(0),
            t2: t_2_blinding,
            t3: t_blinding_factors.remove(0),
            t4: t_blinding_factors.remove(0),
            t5: t_blinding_factors.remove(0),
            t6: t_blinding_factors.remove(0),
        };

        // Evaluate t(x) and \tilde{t}(x) (blinding poly) at the challenge point `x`
        let t_x = t_poly.eval(&x);
        let t_x_blinding = t_blinding_poly.eval(&x);
        let mut l_vec = l_poly.eval(&x);
        l_vec.append(&mut self.fabric.zeros_authenticated(pad));

        let mut r_vec = r_poly.eval(&x);
        r_vec.append(&mut self.fabric.zeros_authenticated(pad));

        // To prove correctness, we need the values y^n * a_r and y^n * s_r (see notes)
        // but the values y^n are not known until after committing to a_r, s_r. So, we
        // change the generator chain H to be y^-n * H; giving us a commitment <y^n * a_r, y^-n * H>
        // Place in a separate closure to limit the borrow's lifetime
        let mut exp_y = -self.fabric.one_authenticated() * exp_y;
        #[allow(clippy::needless_range_loop)]
        for i in n..padded_n {
            r_vec[i] = exp_y.clone();
            exp_y = &exp_y * &y;
        }

        // Take a random linear combination (parameterized by `u`) of the phase 1 and phase 2 blinding factors
        let i_blinding = i_blinding1 + &u * i_blinding2;
        let o_blinding = o_blinding1 + &u * o_blinding2;
        let s_blinding = s_blinding1 + &u * s_blinding2;

        let e_blinding = &x * (i_blinding + &x * (o_blinding + &x * s_blinding));

        // Open the final set of transcript values
        let (t_x_open, t_x_blinding_open, e_blinding_open) = {
            let mut opened_values =
                AuthenticatedScalarResult::open_batch(&[t_x, t_x_blinding, e_blinding]);

            (
                opened_values.remove(0),
                opened_values.remove(0),
                opened_values.remove(0),
            )
        };

        // Append values to transcript
        self.transcript.append_scalar(b"t_x", &t_x_open);
        self.transcript
            .append_scalar(b"t_x_blinding", &t_x_blinding_open);
        self.transcript
            .append_scalar(b"e_blinding", &e_blinding_open);

        // Sample another challenge scalar, this time for the inner product proof
        let w = self.transcript.challenge_scalar(b"w");
        let Q = w * self.pc_gens.B;

        // Chain together the generators from the phase 1 proof and those generators multiplied by
        // `u`; which represent the generators for the phase 2 proof
        let G_factors = iter::repeat(self.fabric.one())
            .take(n1)
            .chain(iter::repeat(u).take(n2 + pad))
            .collect::<Vec<_>>();
        let H_factors = exp_y_inv
            .into_iter()
            .zip(G_factors.iter())
            .map(|(y, u_or_1)| y * u_or_1)
            .collect::<Vec<_>>();

        // Finally, build the inner product proof for the R1CS relation
        let ipp = SharedInnerProductProof::create(
            &mut self.transcript,
            Q,
            &G_factors,
            &H_factors,
            gens.G(padded_n).copied().collect(),
            gens.H(padded_n).copied().collect(),
            l_vec,
            r_vec,
            &self.fabric,
        )?;

        Ok(PartiallySharedR1CSProof {
            A_I1,
            A_O1,
            S1,
            A_I2,
            A_O2,
            S2,
            T_1: T_1.value,
            T_3: T_3.value,
            T_4: T_4.value,
            T_5: T_5.value,
            T_6: T_6.value,
            t_x: t_x_open,
            t_x_blinding: t_x_blinding_open,
            e_blinding: e_blinding_open,
            ipp_proof: ipp,
        })
    }
}
