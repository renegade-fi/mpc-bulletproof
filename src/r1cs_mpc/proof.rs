#![allow(non_snake_case)]
//! Definition of the proof struct.

use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;
use mpc_ristretto::authenticated_ristretto::AuthenticatedCompressedRistretto;
use mpc_ristretto::authenticated_scalar::AuthenticatedScalar;
use mpc_ristretto::beaver::SharedValueSource;
use mpc_ristretto::network::MpcNetwork;

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
pub struct SharedR1CSProof<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> {
    /// Commitment to the values of input wires in the first phase.
    pub(super) A_I1: AuthenticatedCompressedRistretto<N, S>,
    /// Commitment to the values of output wires in the first phase.
    pub(super) A_O1: AuthenticatedCompressedRistretto<N, S>,
    /// Commitment to the blinding factors in the first phase.
    pub(super) S1: AuthenticatedCompressedRistretto<N, S>,
    /// Commitment to the values of input wires in the second phase.
    pub(super) A_I2: AuthenticatedCompressedRistretto<N, S>,
    /// Commitment to the values of output wires in the second phase.
    pub(super) A_O2: AuthenticatedCompressedRistretto<N, S>,
    /// Commitment to the blinding factors in the second phase.
    pub(super) S2: AuthenticatedCompressedRistretto<N, S>,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    pub(super) T_1: AuthenticatedCompressedRistretto<N, S>,
    /// Commitment to the \\(t_3\\) coefficient of \\( t(x) \\)
    pub(super) T_3: AuthenticatedCompressedRistretto<N, S>,
    /// Commitment to the \\(t_4\\) coefficient of \\( t(x) \\)
    pub(super) T_4: AuthenticatedCompressedRistretto<N, S>,
    /// Commitment to the \\(t_5\\) coefficient of \\( t(x) \\)
    pub(super) T_5: AuthenticatedCompressedRistretto<N, S>,
    /// Commitment to the \\(t_6\\) coefficient of \\( t(x) \\)
    pub(super) T_6: AuthenticatedCompressedRistretto<N, S>,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    pub(super) t_x: AuthenticatedScalar<N, S>,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    pub(super) t_x_blinding: AuthenticatedScalar<N, S>,
    /// Blinding factor for the synthetic commitment to the
    /// inner-product arguments
    pub(super) e_blinding: AuthenticatedScalar<N, S>,
    /// Proof data for the inner-product argument.
    pub(super) ipp_proof: SharedInnerProductProof<N, S>,
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> SharedR1CSProof<N, S> {
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
}
