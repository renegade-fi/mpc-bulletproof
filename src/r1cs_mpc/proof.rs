#![allow(non_snake_case)]
//! Definition of the proof struct.

use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;
use mpc_stark::algebra::authenticated_scalar::AuthenticatedScalarResult;
use mpc_stark::algebra::authenticated_stark_point::AuthenticatedStarkPointResult;

use crate::errors::MultiproverError;
use crate::r1cs::R1CSProof;

use super::mpc_inner_product::SharedInnerProductProof;

const ONE_PHASE_COMMITMENTS: u8 = 0;
const TWO_PHASE_COMMITMENTS: u8 = 1;

/// A proof of some statement specified by a
/// [`ConstraintSystem`](::r1cs::ConstraintSystem).
///
/// Statements are specified by writing gadget functions which add
/// constraints to a [`ConstraintSystem`](::r1cs::ConstraintSystem)
/// implementation.  To construct an [`R1CSProof`], a prover constructs
/// a [`ProverCS`](::r1cs::ProverCS), then passes it to gadget
/// functions to build the constraint system, then consumes the
/// constraint system using
/// [`ProverCS::prove`](::r1cs::ProverCS::prove) to produce an
/// [`R1CSProof`].  To verify an [`R1CSProof`], a verifier constructs a
/// [`VerifierCS`](::r1cs::VerifierCS), then passes it to the same
/// gadget functions to (re)build the constraint system, then consumes
/// the constraint system using
/// [`VerifierCS::verify`](::r1cs::VerifierCS::verify) to verify the
/// proof.
#[derive(Clone, Debug)]
#[allow(non_snake_case)]
pub struct SharedR1CSProof {
    /// Commitment to the values of input wires in the first phase.
    pub(super) A_I1: AuthenticatedStarkPointResult,
    /// Commitment to the values of output wires in the first phase.
    pub(super) A_O1: AuthenticatedStarkPointResult,
    /// Commitment to the blinding factors in the first phase.
    pub(super) S1: AuthenticatedStarkPointResult,
    /// Commitment to the values of input wires in the second phase.
    pub(super) A_I2: AuthenticatedStarkPointResult,
    /// Commitment to the values of output wires in the second phase.
    pub(super) A_O2: AuthenticatedStarkPointResult,
    /// Commitment to the blinding factors in the second phase.
    pub(super) S2: AuthenticatedStarkPointResult,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    pub(super) T_1: AuthenticatedStarkPointResult,
    /// Commitment to the \\(t_3\\) coefficient of \\( t(x) \\)
    pub(super) T_3: AuthenticatedStarkPointResult,
    /// Commitment to the \\(t_4\\) coefficient of \\( t(x) \\)
    pub(super) T_4: AuthenticatedStarkPointResult,
    /// Commitment to the \\(t_5\\) coefficient of \\( t(x) \\)
    pub(super) T_5: AuthenticatedStarkPointResult,
    /// Commitment to the \\(t_6\\) coefficient of \\( t(x) \\)
    pub(super) T_6: AuthenticatedStarkPointResult,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    pub(super) t_x: AuthenticatedScalarResult,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    pub(super) t_x_blinding: AuthenticatedScalarResult,
    /// Blinding factor for the synthetic commitment to the
    /// inner-product arguments
    pub(super) e_blinding: AuthenticatedScalarResult,
    /// Proof data for the inner-product argument.
    /// Made public for integration tests to test malleability
    #[cfg(not(feature = "integration_test"))]
    pub(super) ipp_proof: SharedInnerProductProof<N, S>,
    #[cfg(feature = "integration_test")]
    pub ipp_proof: SharedInnerProductProof,
}

impl SharedR1CSProof {
    /// Serializes the proof into a byte array of 1 version byte + \\((13 or 16) + 2k\\) 32-byte elements,
    /// where \\(k=\lceil \log_2(n) \rceil\\) and \\(n\\) is the number of multiplication gates.
    ///
    /// # Layout
    ///
    /// The layout of the r1cs proof encoding is:
    /// * 1 version byte indicating whether the proof contains second-phase commitments or not,
    /// * 8 or 11 compressed Ristretto points \\(A_{I1},A_{O1},S_1,(A_{I2},A_{O2},S_2),T_1,...,T_6\\)
    ///   (\\(A_{I2},A_{O2},S_2\\) are skipped if there were no multipliers added in the randomized phase),
    /// * three scalars \\(t_x, \tilde{t}_x, \tilde{e}\\),
    /// * \\(k\\) pairs of compressed Ristretto points \\(L_0,R_0\dots,L_{k-1},R_{k-1}\\),
    /// * two scalars \\(a, b\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        if self.missing_phase2_commitments() {
            buf.push(ONE_PHASE_COMMITMENTS);
            buf.extend_from_slice(self.A_I1.as_bytes());
            buf.extend_from_slice(self.A_O1.as_bytes());
            buf.extend_from_slice(self.S1.as_bytes());
        } else {
            buf.push(TWO_PHASE_COMMITMENTS);
            buf.extend_from_slice(self.A_I1.as_bytes());
            buf.extend_from_slice(self.A_O1.as_bytes());
            buf.extend_from_slice(self.S1.as_bytes());
            buf.extend_from_slice(self.A_I2.as_bytes());
            buf.extend_from_slice(self.A_O2.as_bytes());
            buf.extend_from_slice(self.S2.as_bytes());
        }
        buf.extend_from_slice(self.T_1.as_bytes());
        buf.extend_from_slice(self.T_3.as_bytes());
        buf.extend_from_slice(self.T_4.as_bytes());
        buf.extend_from_slice(self.T_5.as_bytes());
        buf.extend_from_slice(self.T_6.as_bytes());
        buf.extend_from_slice(self.t_x.as_bytes());
        buf.extend_from_slice(self.t_x_blinding.as_bytes());
        buf.extend_from_slice(self.e_blinding.as_bytes());
        buf.extend(self.ipp_proof.to_bytes_iter());
        buf
    }

    /// Returns the size in bytes required to serialize the `R1CSProof`.
    pub fn serialized_size(&self) -> usize {
        // version tag + (11 or 14) elements + the ipp
        let elements = if self.missing_phase2_commitments() {
            11
        } else {
            14
        };
        1 + elements * 32 + self.ipp_proof.serialized_size()
    }

    fn missing_phase2_commitments(&self) -> bool {
        self.A_I2.is_identity() && self.A_O2.is_identity() && self.S2.is_identity()
    }

    /// Opens the proof, generating a standard R1CS Proof
    pub fn open(&self) -> Result<R1CSProof, MultiproverError> {
        // To open, only the inner product proof must be opened
        // Every other value is opened during the course of proof generation to maintain
        // a consisten Merlin transcript
        let ipp_open = self.ipp_proof.open()?;

        Ok(R1CSProof {
            A_I1: self.A_I1.value(),
            A_O1: self.A_O1.value(),
            S1: self.S1.value(),
            A_I2: self.A_I2.value(),
            A_O2: self.A_O2.value(),
            S2: self.S2.value(),
            T_1: self.T_1.value(),
            T_3: self.T_3.value(),
            T_4: self.T_4.value(),
            T_5: self.T_5.value(),
            T_6: self.T_6.value(),
            t_x: self.t_x.to_scalar(),
            t_x_blinding: self.t_x_blinding.to_scalar(),
            e_blinding: self.e_blinding.to_scalar(),
            ipp_proof: ipp_open,
        })
    }
}
