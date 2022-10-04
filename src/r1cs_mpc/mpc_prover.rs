//! Groups definitions for the MPC prover

use core::{
    cell::{Ref, RefCell},
    iter,
};
use std::net::SocketAddr;

use alloc::rc::Rc;
use curve25519_dalek::{ristretto::CompressedRistretto, scalar::Scalar, traits::Identity};
use merlin::Transcript;
use mpc_ristretto::{
    authenticated_ristretto::{AuthenticatedCompressedRistretto, AuthenticatedRistretto},
    authenticated_scalar::AuthenticatedScalar,
    beaver::SharedValueSource,
    error::MpcError,
    fabric::AuthenticatedMpcFabric,
    network::{MpcNetwork, QuicTwoPartyNet},
    BeaverSource, SharedNetwork,
};

use crate::{
    errors::{MultiproverError, R1CSError},
    r1cs::{
        ConstraintSystem, LinearCombination, RandomizableConstraintSystem,
        RandomizedConstraintSystem, Variable,
    },
    transcript::TranscriptProtocol,
    util, BulletproofGens, PedersenGens,
};

use super::{
    authenticated_poly::{AuthenticatedPoly6, AuthenticatedVecPoly3},
    proof::SharedR1CSProof,
};

/// A convenience wrapper around an MPC fabric with multiple owners
pub(crate) type SharedMpcFabric<N, S> = Rc<RefCell<AuthenticatedMpcFabric<N, S>>>;

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
/// challenges from the protocol transcript that preceeds them. These constraints are encoded in the
/// `deferred_constraints` field.
#[allow(dead_code, non_snake_case)]
pub struct MpcProver<'t, 'g, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> {
    /// The protocol transcript, used for constructing Fiat-Shamir challenges
    transcript: &'t mut Transcript,
    /// Generators used for Pedersen commitments
    pc_gens: &'g PedersenGens,
    /// Teh constraints accumulated so far.
    constraints: Vec<LinearCombination>,
    /// Stores assignments to the "left" of multiplication gates.
    a_L: Vec<AuthenticatedScalar<N, S>>,
    /// Stores assignments to the "right" of multiplication gates.
    a_R: Vec<AuthenticatedScalar<N, S>>,
    /// Stores assignments to the "output" of multiplication gates.
    a_O: Vec<AuthenticatedScalar<N, S>>,
    /// High-level witness assignments (value openings to V commitments)
    /// where we use a pedersen commitment `value * G + blinding * H`
    v: Vec<AuthenticatedScalar<N, S>>,
    /// High level witness data (blinding openings to V commitments)
    v_blinding: Vec<AuthenticatedScalar<N, S>>,
    /// Index of a pending multiplier that hasn't been assigned yet
    pending_multiplier: Option<usize>,
    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    #[allow(clippy::type_complexity)]
    deferred_constraints:
        Vec<Box<dyn Fn(&mut RandomizingMpcProver<'t, 'g, N, S>) -> Result<(), R1CSError>>>,
    /// The MPC Fabric used to allocate values
    mpc_fabric: SharedMpcFabric<N, S>,
}

/// A prover in the randomizing phase.
///
/// In this phase constraints may be built using challenge scalars derived from the
/// protocol transcript so far.
pub struct RandomizingMpcProver<'t, 'g, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> {
    prover: MpcProver<'t, 'g, N, S>,
}

impl<'t, 'g, S: SharedValueSource<Scalar>> MpcProver<'t, 'g, QuicTwoPartyNet, S> {
    /// Create a new MPC prover
    pub fn new(
        party_id: u64,
        local_addr: SocketAddr,
        peer_addr: SocketAddr,
        beaver_source: BeaverSource<S>,
        transcript: &'t mut Transcript,
        pc_gens: &'g PedersenGens,
    ) -> Result<Self, MultiproverError> {
        // Record that we are performing an r1cs proof protocol
        transcript.r1cs_domain_sep();

        // Setup the MPC Fabric to allocate values within
        let mpc_fabric =
            AuthenticatedMpcFabric::new(local_addr, peer_addr, beaver_source, party_id)
                .map_err(|_| MultiproverError::SetupFailed)?;

        Ok(Self {
            transcript,
            pc_gens,
            mpc_fabric: Rc::new(RefCell::new(mpc_fabric)),
            constraints: Vec::new(),
            a_L: Vec::new(),
            a_R: Vec::new(),
            a_O: Vec::new(),
            v: Vec::new(),
            v_blinding: Vec::new(),
            deferred_constraints: Vec::new(),
            pending_multiplier: None,
        })
    }
}

impl<'t, 'g, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> MpcProver<'t, 'g, N, S> {
    /// Create a new MpcProver with a custom network
    pub fn new_with_network(
        party_id: u64,
        network: SharedNetwork<N>,
        beaver_source: BeaverSource<S>,
        transcript: &'t mut Transcript,
        pc_gens: &'g PedersenGens,
    ) -> Self {
        let mpc_fabric = Rc::new(RefCell::new(AuthenticatedMpcFabric::new_with_network(
            party_id,
            network,
            beaver_source,
        )));

        Self {
            transcript,
            pc_gens,
            mpc_fabric,
            constraints: Vec::new(),
            a_L: Vec::new(),
            a_R: Vec::new(),
            a_O: Vec::new(),
            v: Vec::new(),
            v_blinding: Vec::new(),
            deferred_constraints: Vec::new(),
            pending_multiplier: None,
        }
    }

    /// Helper method to borrow the MPC fabric
    fn borrow_fabric(&self) -> Ref<AuthenticatedMpcFabric<N, S>> {
        self.mpc_fabric.as_ref().borrow()
    }

    /// Get the party ID of the local party in the MPC network
    pub fn party_id(&self) -> u64 {
        self.borrow_fabric().party_id()
    }
}

impl<'t, 'g, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> ConstraintSystem
    for MpcProver<'t, 'g, N, S>
{
    /// Lease the transcript to the caller
    fn transcript(&mut self) -> &mut merlin::Transcript {
        self.transcript
    }

    #[allow(unused_variables)]
    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        let l = self.eval(&left);
        let r = self.eval(&right);
        let o = &l * &r;

        // Create new variables for the results
        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());

        // Add the value assignments
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        // Constrain the multiplication
        left.terms.push((l_var, -Scalar::one()));
        right.terms.push((r_var, -Scalar::one()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate(&mut self, assignment: Option<Scalar>) -> Result<Variable, R1CSError> {
        // Allocate a scalar in the MPC network, assume public visibility
        let scalar = assignment.ok_or(R1CSError::MissingAssignment)?;
        let network_scalar = self.borrow_fabric().allocate_public_scalar(scalar);

        // If there is a pending multiplier, allocate this scalar as the right
        // hand side of the multiplication gate
        match self.pending_multiplier {
            None => {
                let i = self.a_L.len();
                self.pending_multiplier = Some(i);
                self.a_L.push(network_scalar);
                let allocated_zero = self.borrow_fabric().allocate_public_scalar(Scalar::zero());
                self.a_R.push(allocated_zero.clone());
                self.a_O.push(allocated_zero);
                Ok(Variable::MultiplierLeft(i))
            }
            Some(i) => {
                self.pending_multiplier = None;
                self.a_R[i] = network_scalar;
                self.a_O[i] = &self.a_L[i] * &self.a_R[i];
                Ok(Variable::MultiplierRight(i))
            }
        }
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        // Allocate a scalar in the MPC network, assume public visibility
        let (left, right) = input_assignments.ok_or(R1CSError::MissingAssignment)?;
        let network_left = self.borrow_fabric().allocate_public_scalar(left);
        let network_right = self.borrow_fabric().allocate_public_scalar(right);

        // Allocate the output of the multiplication gate
        self.a_O.push(&network_left * &network_right);
        self.a_L.push(network_left);
        self.a_R.push(network_right);

        Ok((
            Variable::MultiplierLeft(self.a_L.len() - 1),
            Variable::MultiplierRight(self.a_R.len() - 1),
            Variable::MultiplierOutput(self.a_O.len() - 1),
        ))
    }

    fn multipliers_len(&self) -> usize {
        self.a_L.len()
    }

    fn constrain(&mut self, lc: LinearCombination) {
        self.constraints.push(lc)
    }
}

impl<'t, 'g, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> RandomizableConstraintSystem
    for MpcProver<'t, 'g, N, S>
{
    type RandomizedCS = RandomizingMpcProver<'t, 'g, N, S>;

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        F: 'static + Fn(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        self.deferred_constraints.push(Box::new(callback));
        Ok(())
    }
}

impl<'t, 'g, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> ConstraintSystem
    for RandomizingMpcProver<'t, 'g, N, S>
{
    fn transcript(&mut self) -> &mut Transcript {
        self.prover.transcript()
    }

    fn multiply(
        &mut self,
        left: LinearCombination,
        right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        self.prover.multiply(left, right)
    }

    fn allocate(&mut self, assignment: Option<Scalar>) -> Result<Variable, R1CSError> {
        self.prover.allocate(assignment)
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        self.prover.allocate_multiplier(input_assignments)
    }

    fn multipliers_len(&self) -> usize {
        self.prover.multipliers_len()
    }

    fn constrain(&mut self, lc: LinearCombination) {
        self.prover.constrain(lc)
    }
}

impl<'t, 'g, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> RandomizedConstraintSystem
    for RandomizingMpcProver<'t, 'g, N, S>
{
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.prover.transcript.challenge_scalar(label)
    }
}

impl<'t, 'g, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> MpcProver<'t, 'g, N, S> {
    /// Evaluate a linear combination of allocated variables
    fn eval(&self, lc: &LinearCombination) -> AuthenticatedScalar<N, S> {
        lc.terms.iter().fold(
            self.borrow_fabric().allocate_public_u64(0),
            |acc, (var, coeff)| {
                acc + match var {
                    Variable::MultiplierLeft(i) => *coeff * &self.a_L[*i],
                    Variable::MultiplierRight(i) => *coeff * &self.a_R[*i],
                    Variable::MultiplierOutput(i) => *coeff * &self.a_O[*i],
                    Variable::Committed(i) => *coeff * &self.v[*i],
                    Variable::One() => *coeff * self.borrow_fabric().allocate_public_u64(1),
                }
            },
        )
    }

    /// From a privately held input value, secret share the value and commit to it
    ///
    /// The result is a variable allocated both in the MPC network and in the
    /// constraint system; along with its respectively commitment.
    pub fn commit(
        &mut self,
        owning_party: u64,
        v: Scalar,
        v_blinding: Scalar,
    ) -> Result<(AuthenticatedCompressedRistretto<N, S>, Variable), MpcError> {
        // Allocate the value in the MPC network
        let shared_v = self
            .borrow_fabric()
            .allocate_private_scalar(owning_party, v)?;
        let shared_v_blinding = self
            .borrow_fabric()
            .allocate_private_scalar(owning_party, v_blinding)?;

        // Add the commitment to the transcript.
        let value_commit = self
            .pc_gens
            .commit_shared(&shared_v, &shared_v_blinding)
            .compress();
        self.transcript.append_point(b"V", &value_commit.value());

        // Add the value to the constraint system
        let i = self.v.len();
        self.v.push(shared_v);
        self.v_blinding.push(shared_v_blinding);

        Ok((value_commit, Variable::Committed(i)))
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
        z: &Scalar,
    ) -> (
        Vec<AuthenticatedScalar<N, S>>,
        Vec<AuthenticatedScalar<N, S>>,
        Vec<AuthenticatedScalar<N, S>>,
        Vec<AuthenticatedScalar<N, S>>,
    ) {
        let n = self.a_L.len();
        let m = self.v.len();

        let mut wL = self.borrow_fabric().allocate_zeros(n);
        let mut wR = self.borrow_fabric().allocate_zeros(n);
        let mut wO = self.borrow_fabric().allocate_zeros(n);
        let mut wV = self.borrow_fabric().allocate_zeros(m);

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::MultiplierLeft(i) => {
                        wL[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierRight(i) => {
                        wR[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierOutput(i) => {
                        wO[*i] += exp_z * coeff;
                    }
                    Variable::Committed(i) => {
                        wV[*i] -= exp_z * coeff;
                    }
                    Variable::One() => {
                        // The prover doesn't need to handle constant terms
                    }
                }
            }
            exp_z *= z;
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

    /// Consume this `ConstraintSystem` and produce a shared proof
    /// TODO: Remove these clippy allowances
    ///
    /// Throughout proof generation we open intermediate proof results that go into
    /// the transcript. This is in order to keep the transcripts of the provers in sync
    /// as they derive Fiat-Shamir challenges from these transcripts. This is simpler
    /// than deriving the challenges in secret sharing space as we would have to hash
    /// within the MPC circuit, and implement a hasher on top of the authenticated field.
    #[allow(non_snake_case, unused_variables, unused_mut)]
    pub fn prove(
        mut self,
        bp_gens: &BulletproofGens,
    ) -> Result<SharedR1CSProof<N, S>, MultiproverError> {
        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.transcript.append_u64(b"m", self.v.len() as u64);

        // Create a `TranscriptRng` from the high-level witness data
        //
        // The prover wants to rekey the RNG with its witness data.
        //
        // This consists of the high level witness data (the v's and
        // v_blinding's), as well as the low-level witness data (a_L,
        // a_R, a_O).  Since the low-level data should (hopefully) be
        // determined by the high-level data, it doesn't give any
        // extra entropy for reseeding the RNG.
        //
        // Since the v_blindings should be random scalars (in order to
        // protect the v's in the commitments), we don't gain much by
        // committing the v's as well as the v_blinding's.
        let mut rng = {
            let mut builder = self.transcript.build_rng();

            // Commit the blinding factors for the input wires
            for v_b in &self.v_blinding {
                builder = builder.rekey_with_witness_bytes(b"v_blinding", v_b.as_bytes());
            }

            use rand::thread_rng;
            builder.finalize(&mut thread_rng())
        };

        // Commit to the low-level witness data, a_l, a_r, a_o in the multiplication
        // gates.
        // Both parties use the same generator chain here. We do this to avoid communication
        // overhead; as a multiscalar mul with a public generator chain will not induce
        // communication, all Pedersen commitments can be computed locally.
        let gens = bp_gens.as_mpc_values(self.mpc_fabric.clone());

        // Multiplicative depth of the circuit
        let n1 = self.a_L.len();

        // Allow party 0 to generate the blinding factors and distribute the shares
        // We need 2n1 + 3 blinding factors, 3 for commitments to A_I (inputs) and A_O (outputs)
        // and n1 for each of the s_L, s_R terms that are used to blind a_L and a_R directly.
        let blinding_factors = self
            .borrow_fabric()
            .allocate_random_scalars_batch(3 + 2 * n1);

        let (i_blinding1, o_blinding1, s_blinding1) = (
            blinding_factors[0].clone(),
            blinding_factors[1].clone(),
            blinding_factors[2].clone(),
        );

        let mut s_L1 = blinding_factors[3..3 + n1].to_vec();
        let mut s_R1 = blinding_factors[3 + n1..3 + 2 * n1].to_vec();

        // Allocate the Pedersen blinding generator in the network
        let B_blinding = self
            .borrow_fabric()
            .allocate_public_ristretto_point(self.pc_gens.B_blinding);

        // Construct a commitment to the multiplication gate inputs a_L and a_R
        // This commitment has the form:
        //      A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
        // where G and H are the vectors of generators for the curve group, and B_blinding
        // is the blinding Pedersen generator.
        let A_I1 = AuthenticatedRistretto::multiscalar_mul(
            iter::once(&i_blinding1)
                .chain(self.a_L.iter())
                .chain(self.a_R.iter()),
            iter::once(B_blinding.clone())
                .chain(gens.G(n1))
                .chain(gens.H(n1)),
        )
        .open_and_authenticate()
        .map_err(MultiproverError::Mpc)?
        .compress();

        // Construct a commitment to the multiplication gate outputs a_O
        // This commitment has the form
        //      A_O = <a_O, G> + o_blinding * B_blinding
        // where G is a vector of generators for the curve group, and B_blinding
        // is the blinding Pedersen generator.
        let A_O1 = AuthenticatedRistretto::multiscalar_mul(
            iter::once(&o_blinding1).chain(self.a_O.iter()),
            iter::once(B_blinding.clone()).chain(gens.G(n1)),
        )
        .open_and_authenticate()
        .map_err(MultiproverError::Mpc)?
        .compress();

        // Construct a commitment to the blinding factors used in the inner product proofs
        // This commitment has the form
        //    S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        // where G, H, and B_blinding are generators as above. s_L and s_R are vectors of blinding
        // factors used to hide a_L and a_R in the inner product proofs respectively.
        let S1 = AuthenticatedRistretto::multiscalar_mul(
            iter::once(&s_blinding1)
                .chain(s_L1.iter())
                .chain(s_R1.iter()),
            iter::once(B_blinding.clone())
                .chain(gens.G(n1))
                .chain(gens.H(n1)),
        )
        .open_and_authenticate()
        .map_err(MultiproverError::Mpc)?
        .compress();

        // Add the commitments to the transcript, these are used to generate Fiat-Shamir challenges
        self.transcript.append_point(b"A_I1", &A_I1.value());
        self.transcript.append_point(b"A_O1", &A_O1.value());
        self.transcript.append_point(b"S1", &S1.value());

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
        let blinding_factors = self
            .borrow_fabric()
            .allocate_random_scalars_batch(3 + 2 * n2);

        let (i_blinding2, o_blinding2, s_blinding2) = (
            blinding_factors[0].clone(),
            blinding_factors[1].clone(),
            blinding_factors[2].clone(),
        );

        let mut s_L2 = blinding_factors[3..3 + n2].to_vec();
        let mut s_R2 = blinding_factors[3 + n2..3 + 2 * n2].to_vec();

        // Commit to the second phase input, outputs, and blinding factors as above
        // If there are no second phase commitments, we can skip this and reutrn the identity
        let (A_I2, A_O2, S2) = if has_2nd_phase_commitments {
            // Commit to the left and right inputs to the multiplication gates from phase 2
            // This commitment has the form:
            //      A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
            // where G and H are the vectors of generators for the curve group, and B_blinding
            // is the blinding Pedersen generator.
            let shared_A_I = AuthenticatedRistretto::multiscalar_mul(
                iter::once(&i_blinding2)
                    .chain(self.a_L.iter().skip(n1))
                    .chain(self.a_R.iter().skip(n1)),
                iter::once(B_blinding.clone())
                    .chain(gens.G(n).skip(n1))
                    .chain(gens.H(n).skip(n1)),
            );
            // Commit to the outputs of the multiplication gates from phase 2
            // This commitment has the form
            //      A_O = <a_O, G> + o_blinding * B_blinding
            // where G is a vector of generators for the curve group, and B_blinding
            // is the blinding Pedersen generator.
            let shared_A_O = AuthenticatedRistretto::multiscalar_mul(
                iter::once(&o_blinding2).chain(self.a_O.iter().skip(n1)),
                iter::once(B_blinding.clone()).chain(gens.G(n).skip(n1)),
            );
            // Commit to the blinding factors used in the inner product proofs
            // This commitment has the form
            //    S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
            // where G, H, and B_blinding are generators as above. s_L and s_R are vectors of blinding
            // factors used to hide a_L and a_R in the inner product proofs respectively.
            let shared_S = AuthenticatedRistretto::multiscalar_mul(
                iter::once(&s_blinding2)
                    .chain(s_L2.iter())
                    .chain(s_R2.iter()),
                iter::once(B_blinding)
                    .chain(gens.G(n).skip(n1))
                    .chain(gens.H(n).skip(n1)),
            );

            // Batch open the values
            let opened_values = AuthenticatedRistretto::batch_open_and_authenticate(&[
                shared_A_I, shared_A_O, shared_S,
            ])
            .map_err(MultiproverError::Mpc)?;

            (
                opened_values[0].compress(),
                opened_values[1].compress(),
                opened_values[2].compress(),
            )
        } else {
            (
                self.borrow_fabric()
                    .allocate_public_compressed_ristretto(CompressedRistretto::identity()),
                self.borrow_fabric()
                    .allocate_public_compressed_ristretto(CompressedRistretto::identity()),
                self.borrow_fabric()
                    .allocate_public_compressed_ristretto(CompressedRistretto::identity()),
            )
        };

        // Add the commitments to the transcript
        self.transcript.append_point(b"A_I2", &A_I2.value());
        self.transcript.append_point(b"A_O2", &A_O2.value());
        self.transcript.append_point(b"S2", &S2.value());

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
        // substitues in the expected value for t_2
        let mut l_poly = AuthenticatedVecPoly3::zero(n, self.mpc_fabric.clone());
        let mut r_poly = AuthenticatedVecPoly3::zero(n, self.mpc_fabric.clone());

        // A sequence of challenge scalars for a_l \dot a_r - a_o
        // These challenges are public values, we can invert and construct them as plain scalars
        // and then wrap them in network allocated values.
        let mut exp_y = Scalar::one();
        let y_inv = y.invert();
        let exp_y_inv = util::exp_iter(y_inv).take(padded_n).collect::<Vec<_>>();

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
            l_poly.1[i] = &self.a_L[i] + exp_y_inv[i] * &wR[i];
            // 2nd degree coefficient is: a_o
            l_poly.2[i] = self.a_O[i].clone();
            // 3rd degree coefficient is: s_L
            l_poly.3[i] = sl.clone();

            // 0th degree coefficient is: w_o - y^n
            r_poly.0[i] = &wO[i] - exp_y;
            // 1st degree coefficient is: y^n * a_r + w_l
            r_poly.1[i] = exp_y * &self.a_R[i] + &wL[i];
            // 2nd degree coefficient is: 0
            // 3rd degree coefficient is: y^n * s_R
            r_poly.3[i] = exp_y * sr;

            // Incrementally exponentiate the challenge scalar `y`
            exp_y *= y;
        }

        // The core of the proof is two fold. Let the polynomial below be t(x) = <l(x), r(x)>; we prove:
        //      1. That the second degree coefficient of t(x) equals the public verifier input, encoding
        //         the R1CS constraint system's assignment
        //      2. An inner product proof that t(x) = <l(x), r(x)>
        let t_poly = AuthenticatedVecPoly3::special_inner_product(&l_poly, &r_poly);
        let t_blinding_factors = self.borrow_fabric().allocate_random_scalars_batch(5);

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
                .commit_shared(&t_poly.t6, &t_blinding_factors[5]);

            let opened_values = AuthenticatedRistretto::batch_open_and_authenticate(&[
                t_1_shared, t_3_shared, t_4_shared, t_5_shared, t_6_shared,
            ])
            .map_err(MultiproverError::Mpc)?;

            (
                opened_values[0].clone(),
                opened_values[1].clone(),
                opened_values[2].clone(),
                opened_values[3].clone(),
                opened_values[4].clone(),
            )
        };

        // Add the commitments to the transcript
        self.transcript
            .append_point(b"T_1", &T_1.to_ristretto().compress());
        self.transcript
            .append_point(b"T_3", &T_3.to_ristretto().compress());
        self.transcript
            .append_point(b"T_4", &T_4.to_ristretto().compress());
        self.transcript
            .append_point(b"T_5", &T_5.to_ristretto().compress());
        self.transcript
            .append_point(b"T_6", &T_6.to_ristretto().compress());

        // Sample two more challenge scalars:
        //    - `u` is used to create a random linear combination of the non-randomized and randomized
        //      commitments to the polynomials l(x) and r(x). The randomized component comes from the
        //      deferred constraints, evaluated above
        //    - `x` is used to construct the challenge point `X` for the inner product proof
        let u = self.transcript.challenge_scalar(b"u");
        let x_scalar = self.transcript.challenge_scalar(b"x");
        let x = self.borrow_fabric().allocate_public_scalar(x_scalar);

        // Because we do not commit to T_2 directly, we commit to its replacement blinding factor that
        // will satisfy the equality: https://doc-internal.dalek.rs/bulletproofs/notes/r1cs_proof/index.html#proving-that-t_2-is-correct
        let t_2_blinding: AuthenticatedScalar<N, S> = wV
            .iter()
            .zip(self.v_blinding.iter())
            .map(|(c, v_blinding)| c * v_blinding)
            .sum();

        let t_blinding_poly = AuthenticatedPoly6 {
            t1: blinding_factors[0].clone(),
            t2: t_2_blinding,
            t3: blinding_factors[1].clone(),
            t4: blinding_factors[2].clone(),
            t5: blinding_factors[3].clone(),
            t6: blinding_factors[4].clone(),
        };

        // Evaluate t(x) and \tilde{t}(x) (blinding poly) at the challenge point `x`
        let t_x = t_poly.eval(&x);
        let t_x_blinding = t_blinding_poly.eval(&x);
        let mut l_vec = l_poly.eval(&x);
        l_vec.append(&mut self.borrow_fabric().allocate_zeros(pad));

        let mut r_vec = r_poly.eval(&x);
        r_vec.append(&mut self.borrow_fabric().allocate_zeros(pad));

        // To prove correctness, we need the values y^n * a_r and y^n * s_r (see notes)
        // but the values y^n are not known until after committing to a_r, s_r. So, we
        // change the generator chain H to be y^-n * H; giving us a commitment <y^n * a_r, y^-n * H>
        // Place in a separate closure to limit the borrow's liftime
        {
            let borrowed_fabric = self.borrow_fabric();
            #[allow(clippy::needless_range_loop)]
            for i in n..padded_n {
                r_vec[i] = borrowed_fabric.allocate_public_scalar(-exp_y);
                exp_y *= y;
            }
        } // borrowed_fabric lifetime finished

        // Take a random linear combination (parameterized by `u`) of the phase 1 and phase 2 blinding factors
        let i_blinding = i_blinding1 + u * i_blinding2;
        let o_blinding = o_blinding1 + u * o_blinding2;
        let s_blinding = s_blinding1 + u * s_blinding2;

        let e_blinding = &x * (i_blinding + &x * (o_blinding + &x * s_blinding));

        // Open the final set of transcript values
        let (t_x_open, t_x_blinding_open, e_blinding_open) = {
            let opened_values =
                AuthenticatedScalar::batch_open_and_authenticate(&[t_x, t_x_blinding, e_blinding])
                    .map_err(MultiproverError::Mpc)?;

            (
                opened_values[0].clone(),
                opened_values[1].clone(),
                opened_values[2].clone(),
            )
        };

        // Append values to transcript
        self.transcript.append_scalar(b"t_x", &t_x_open.to_scalar());
        self.transcript
            .append_scalar(b"t_x_blinding", &t_x_blinding_open.to_scalar());
        self.transcript
            .append_scalar(b"e_blinding", &e_blinding_open.to_scalar());

        // Sample another challenge scalar, this time for the inner product proof
        let w = self.transcript.challenge_scalar(b"w");
        let Q = w * self.pc_gens.B;

        // Chain together the generators from the phase 1 proof and those generators multiplied by
        // `u`; which represent the generators for the phase 2 proof
        let G_factors = iter::repeat(Scalar::one())
            .take(n1)
            .chain(iter::repeat(u).take(n2 + pad))
            .collect::<Vec<_>>();
        let H_factors = exp_y_inv
            .into_iter()
            .zip(G_factors.iter())
            .map(|(y, u_or_1)| y * u_or_1)
            .collect::<Vec<_>>();

        // Finally, build the inner product proof for the R1CS relation
        // TODO: IPP

        Err(MultiproverError::NotImplemented)
    }
}
