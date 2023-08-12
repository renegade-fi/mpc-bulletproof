#![allow(non_snake_case)]
//! Definition of the proof struct.

use mpc_stark::algebra::scalar::{Scalar, SCALAR_BYTES};
use mpc_stark::algebra::stark_curve::{StarkPoint, STARK_POINT_BYTES};

use crate::errors::R1CSError;
use crate::inner_product_proof::InnerProductProof;
use crate::util;

use serde::de::Visitor;
use serde::{self, Deserialize, Deserializer, Serialize, Serializer};

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
pub struct R1CSProof {
    /// Commitment to the values of input wires in the first phase.
    pub(crate) A_I1: StarkPoint,
    /// Commitment to the values of output wires in the first phase.
    pub(crate) A_O1: StarkPoint,
    /// Commitment to the blinding factors in the first phase.
    pub(crate) S1: StarkPoint,
    /// Commitment to the values of input wires in the second phase.
    pub(crate) A_I2: StarkPoint,
    /// Commitment to the values of output wires in the second phase.
    pub(crate) A_O2: StarkPoint,
    /// Commitment to the blinding factors in the second phase.
    pub(crate) S2: StarkPoint,
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    pub(crate) T_1: StarkPoint,
    /// Commitment to the \\(t_3\\) coefficient of \\( t(x) \\)
    pub(crate) T_3: StarkPoint,
    /// Commitment to the \\(t_4\\) coefficient of \\( t(x) \\)
    pub(crate) T_4: StarkPoint,
    /// Commitment to the \\(t_5\\) coefficient of \\( t(x) \\)
    pub(crate) T_5: StarkPoint,
    /// Commitment to the \\(t_6\\) coefficient of \\( t(x) \\)
    pub(crate) T_6: StarkPoint,
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    pub(crate) t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    pub(crate) t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the
    /// inner-product arguments
    pub(crate) e_blinding: Scalar,
    /// Proof data for the inner-product argument.
    pub(crate) ipp_proof: InnerProductProof,
}

impl R1CSProof {
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
            buf.extend_from_slice(&self.A_I1.to_bytes());
            buf.extend_from_slice(&self.A_O1.to_bytes());
            buf.extend_from_slice(&self.S1.to_bytes());
        } else {
            buf.push(TWO_PHASE_COMMITMENTS);
            buf.extend_from_slice(&self.A_I1.to_bytes());
            buf.extend_from_slice(&self.A_O1.to_bytes());
            buf.extend_from_slice(&self.S1.to_bytes());
            buf.extend_from_slice(&self.A_I2.to_bytes());
            buf.extend_from_slice(&self.A_O2.to_bytes());
            buf.extend_from_slice(&self.S2.to_bytes());
        }
        buf.extend_from_slice(&self.T_1.to_bytes());
        buf.extend_from_slice(&self.T_3.to_bytes());
        buf.extend_from_slice(&self.T_4.to_bytes());
        buf.extend_from_slice(&self.T_5.to_bytes());
        buf.extend_from_slice(&self.T_6.to_bytes());
        buf.extend_from_slice(&self.t_x.to_bytes_be());
        buf.extend_from_slice(&self.t_x_blinding.to_bytes_be());
        buf.extend_from_slice(&self.e_blinding.to_bytes_be());
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

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `R1CSProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<R1CSProof, R1CSError> {
        if slice.is_empty() {
            return Err(R1CSError::FormatError);
        }
        let version = slice[0];
        let mut slice = &slice[1..];

        if slice.len() % 32 != 0 {
            return Err(R1CSError::FormatError);
        }

        let minlength = match version {
            ONE_PHASE_COMMITMENTS => 11 * 32,
            TWO_PHASE_COMMITMENTS => 14 * 32,
            _ => return Err(R1CSError::FormatError),
        };

        if slice.len() < minlength {
            return Err(R1CSError::FormatError);
        }

        // This macro takes care of counting bytes in the slice
        macro_rules! read_point {
            () => {{
                let tmp = util::read_exact::<STARK_POINT_BYTES>(slice);
                slice = &slice[STARK_POINT_BYTES..];
                StarkPoint::from_bytes(&tmp).map_err(|_| R1CSError::FormatError)
            }};
        }

        macro_rules! read_scalar {
            () => {{
                let tmp = util::read_exact::<SCALAR_BYTES>(slice);
                slice = &slice[SCALAR_BYTES..];
                Scalar::from_be_bytes_mod_order(&tmp)
            }};
        }

        let A_I1 = read_point!()?;
        let A_O1 = read_point!()?;
        let S1 = read_point!()?;
        let (A_I2, A_O2, S2) = if version == ONE_PHASE_COMMITMENTS {
            (
                StarkPoint::identity(),
                StarkPoint::identity(),
                StarkPoint::identity(),
            )
        } else {
            (read_point!()?, read_point!()?, read_point!()?)
        };
        let T_1 = read_point!()?;
        let T_3 = read_point!()?;
        let T_4 = read_point!()?;
        let T_5 = read_point!()?;
        let T_6 = read_point!()?;
        let t_x = read_scalar!();
        let t_x_blinding = read_scalar!();
        let e_blinding = read_scalar!();

        // XXX: IPPProof from_bytes gives ProofError.
        let ipp_proof = InnerProductProof::from_bytes(slice).map_err(|_| R1CSError::FormatError)?;

        Ok(R1CSProof {
            A_I1,
            A_O1,
            S1,
            A_I2,
            A_O2,
            S2,
            T_1,
            T_3,
            T_4,
            T_5,
            T_6,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        })
    }
}

impl Serialize for R1CSProof {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

impl<'de> Deserialize<'de> for R1CSProof {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct R1CSProofVisitor;

        impl<'de> Visitor<'de> for R1CSProofVisitor {
            type Value = R1CSProof;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("a valid R1CSProof")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut bytes = Vec::with_capacity(seq.size_hint().unwrap_or(100 /* default */));
                while let Ok(Some(next_byte)) = seq.next_element::<u8>() {
                    bytes.push(next_byte)
                }

                R1CSProof::from_bytes(&bytes).map_err(serde::de::Error::custom)
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<R1CSProof, E>
            where
                E: serde::de::Error,
            {
                // Using Error::custom requires T: Display, which our error
                // type only implements when it implements std::error::Error.
                #[cfg(feature = "std")]
                return R1CSProof::from_bytes(v).map_err(serde::de::Error::custom);
                // In no-std contexts, drop the error message.
                #[cfg(not(feature = "std"))]
                return R1CSProof::from_bytes(v)
                    .map_err(|_| serde::de::Error::custom("deserialization error"));
            }
        }

        deserializer.deserialize_bytes(R1CSProofVisitor)
    }
}
