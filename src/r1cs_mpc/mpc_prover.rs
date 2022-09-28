//! Groups definitions for the MPC prover

use std::net::SocketAddr;

use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use mpc_ristretto::{
    authenticated_scalar::AuthenticatedScalar,
    beaver::SharedValueSource,
    fabric::AuthenticatedMpcFabric,
    network::{MpcNetwork, QuicTwoPartyNet},
    BeaverSource, SharedNetwork,
};

use crate::{
    errors::{MultiproverError, R1CSError},
    r1cs::{ConstraintSystem, LinearCombination, Variable},
    transcript::TranscriptProtocol,
    PedersenGens,
};

/// An implementation of a collaborative Bulletproof prover.
///
/// This prover represents one peer in an MPC network. Together
/// with one (or more) peers, it generates a proof of knowledge
/// of satisfying witness for a given R1CS relation.
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
    /// The MPC Fabric used to allocate values
    mpc_fabric: AuthenticatedMpcFabric<N, S>,
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
            mpc_fabric,
            constraints: Vec::new(),
            a_L: Vec::new(),
            a_R: Vec::new(),
            a_O: Vec::new(),
            v: Vec::new(),
            v_blinding: Vec::new(),
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
        Self {
            transcript,
            pc_gens,
            mpc_fabric: AuthenticatedMpcFabric::new_with_network(party_id, network, beaver_source),
            constraints: Vec::new(),
            a_L: Vec::new(),
            a_R: Vec::new(),
            a_O: Vec::new(),
            v: Vec::new(),
            v_blinding: Vec::new(),
            pending_multiplier: None,
        }
    }

    /// Get the party ID of the local party in the MPC network
    pub fn party_id(&self) -> u64 {
        self.mpc_fabric.party_id()
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
        let network_scalar = self.mpc_fabric.allocate_public_scalar(scalar);

        // If there is a pending multiplier, allocate this scalar as the right
        // hand side of the multiplication gate
        match self.pending_multiplier {
            None => {
                let i = self.a_L.len();
                self.pending_multiplier = Some(i);
                self.a_L.push(network_scalar);
                self.a_R
                    .push(self.mpc_fabric.allocate_public_scalar(Scalar::zero()));
                self.a_O
                    .push(self.mpc_fabric.allocate_public_scalar(Scalar::zero()));
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
        let network_left = self.mpc_fabric.allocate_public_scalar(left);
        let network_right = self.mpc_fabric.allocate_public_scalar(right);

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

impl<'t, 'g, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> MpcProver<'t, 'g, N, S> {
    fn eval(&self, lc: &LinearCombination) -> AuthenticatedScalar<N, S> {
        lc.terms.iter().fold(
            self.mpc_fabric.allocate_public_u64(0),
            |acc, (var, coeff)| {
                acc + match var {
                    Variable::MultiplierLeft(i) => *coeff * &self.a_L[*i],
                    Variable::MultiplierRight(i) => *coeff * &self.a_R[*i],
                    Variable::MultiplierOutput(i) => *coeff * &self.a_O[*i],
                    Variable::Committed(i) => *coeff * &self.v[*i],
                    Variable::One() => *coeff * self.mpc_fabric.allocate_public_u64(1),
                }
            },
        )
    }
}
