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
    BulletproofGens, PedersenGens,
};

use super::proof::SharedR1CSProof;

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
            .allocate_random_scalars_batch(3 + 2 * n1, &mut rng)
            .map_err(MultiproverError::Mpc)?;

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
        .compress();

        // Construct a commitment to the blinding factors used in the inner product proofs
        // This commitment has the form
        //    A_S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
        // where G, H, and B_blinding are generators as above. s_L and s_R are vectors of blinding
        // factors used to hide a_L and a_R in the inner product proofs respectively.
        let A_S1 = AuthenticatedRistretto::multiscalar_mul(
            iter::once(&s_blinding1)
                .chain(s_L1.iter())
                .chain(s_R1.iter()),
            iter::once(B_blinding.clone())
                .chain(gens.G(n1))
                .chain(gens.H(n1)),
        )
        .compress();

        // Add the commitments to the transcript, these are used to generate Fiat-Shamir challenges
        self.transcript.append_point(b"A_I1", &A_I1.value());
        self.transcript.append_point(b"A_O1", &A_O1.value());
        self.transcript.append_point(b"S1", &A_S1.value());

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
            .allocate_random_scalars_batch(3 + 2 * n2, &mut rng)
            .map_err(MultiproverError::Mpc)?;

        let (i_blinding2, o_blinding2, s_blinding2) = (
            blinding_factors[0].clone(),
            blinding_factors[1].clone(),
            blinding_factors[2].clone(),
        );

        let mut s_L2 = blinding_factors[3..3 + n2].to_vec();
        let mut s_R2 = blinding_factors[3 + n2..3 + 2 * n2].to_vec();

        // Commit to the second phase input, outputs, and blinding factors as above
        // If there are no second phase commitments, we can skip this and reutrn the identity
        let (A_I2, A_O2, A_S2) = if has_2nd_phase_commitments {
            (
                // Commit to the left and right inputs to the multiplication gates from phase 2
                // This commitment has the form:
                //      A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
                // where G and H are the vectors of generators for the curve group, and B_blinding
                // is the blinding Pedersen generator.
                AuthenticatedRistretto::multiscalar_mul(
                    iter::once(&i_blinding2)
                        .chain(self.a_L.iter().skip(n1))
                        .chain(self.a_R.iter().skip(n1)),
                    iter::once(B_blinding.clone())
                        .chain(gens.G(n).skip(n1))
                        .chain(gens.H(n).skip(n1)),
                )
                .compress(),
                // Commit to the outputs of the multiplication gates from phase 2
                // This commitment has the form
                //      A_O = <a_O, G> + o_blinding * B_blinding
                // where G is a vector of generators for the curve group, and B_blinding
                // is the blinding Pedersen generator.
                AuthenticatedRistretto::multiscalar_mul(
                    iter::once(&o_blinding2).chain(self.a_O.iter().skip(n1)),
                    iter::once(B_blinding.clone()).chain(gens.G(n).skip(n1)),
                )
                .compress(),
                // Commit to the blinding factors used in the inner product proofs
                // This commitment has the form
                //    A_S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
                // where G, H, and B_blinding are generators as above. s_L and s_R are vectors of blinding
                // factors used to hide a_L and a_R in the inner product proofs respectively.
                AuthenticatedRistretto::multiscalar_mul(
                    iter::once(&s_blinding2)
                        .chain(s_L2.iter())
                        .chain(s_R2.iter()),
                    iter::once(B_blinding)
                        .chain(gens.G(n).skip(n1))
                        .chain(gens.H(n).skip(n1)),
                )
                .compress(),
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

        Err(MultiproverError::NotImplemented)
    }
}
