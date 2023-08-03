//! Groups the implementation of inner product proofs over an authenticated
//! scalar field

#![allow(non_snake_case)]
#![doc = include_str!("../../docs/inner-product-protocol.md")]

extern crate alloc;

use alloc::vec::Vec;
use futures::future::join_all;
use mpc_stark::algebra::authenticated_scalar::AuthenticatedScalarResult;
use mpc_stark::algebra::authenticated_stark_point::AuthenticatedStarkPointOpenResult;
use mpc_stark::algebra::scalar::{Scalar, ScalarResult};
use mpc_stark::algebra::stark_curve::{StarkPoint, StarkPointResult};
use mpc_stark::error::MpcError;
use mpc_stark::MpcFabric;

use core::iter;

use crate::errors::MultiproverError;
use crate::inner_product_proof::InnerProductProof;
use crate::transcript::MpcTranscript;

/// An inner product proof that is secret shared between multiple proving parties.
///
/// This type does not include a verifier implementation; verification should happen
/// via the standard Bulletproof verifier defined in the parent module.
#[derive(Clone, Debug)]
pub struct SharedInnerProductProof {
    pub(crate) L_vec: Vec<AuthenticatedStarkPointOpenResult>,
    pub(crate) R_vec: Vec<AuthenticatedStarkPointOpenResult>,
    /// Only expose `a` and `b` for integration tests, testing malleability
    #[cfg(not(feature = "integration_test"))]
    pub(crate) a: AuthenticatedScalarResult,
    #[cfg(feature = "integration_test")]
    pub a: AuthenticatedScalarResult,
    #[cfg(not(feature = "integration_test"))]
    pub(crate) b: AuthenticatedScalarResult,
    #[cfg(feature = "integration_test")]
    pub b: AuthenticatedScalarResult,
}

#[allow(clippy::too_many_arguments)]
impl SharedInnerProductProof {
    /// Create an inner-product proof.
    ///
    /// The proof is created with respect to the bases \\(G\\), \\(H'\\),
    /// where \\(H'\_i = H\_i \cdot \text{H^\prime\\_factors}\_i\\).
    ///
    /// The lengths of the vectors must all be the same, and must all be
    /// either 0 or a power of 2.
    pub fn create(
        transcript: &mut MpcTranscript,
        Q: StarkPointResult,
        G_factors: &[ScalarResult],
        H_factors: &[ScalarResult],
        mut G_vec: Vec<StarkPoint>,
        mut H_vec: Vec<StarkPoint>,
        mut a_vec: Vec<AuthenticatedScalarResult>,
        mut b_vec: Vec<AuthenticatedScalarResult>,
        fabric: &MpcFabric,
    ) -> Result<SharedInnerProductProof, MultiproverError> {
        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us re-slice as we compress the lengths
        // of the vectors in the main loop below.
        let G = &mut G_vec[..];
        let H = &mut H_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let mut n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert_eq!(G_factors.len(), n);
        assert_eq!(H_factors.len(), n);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());

        transcript.innerproduct_domain_sep(n as u64);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        // If it's the first iteration, unroll the Hprime = H*y_inv scalar multiplications
        // into multiscalar muls, for performance.
        let mut G_res = Vec::with_capacity(n / 2);
        let mut H_res = Vec::with_capacity(n / 2);
        if n != 1 {
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = authenticated_inner_product(a_L, b_R, fabric.clone());
            let c_R = authenticated_inner_product(a_R, b_L, fabric.clone());

            let L = StarkPoint::msm_authenticated_iter(
                a_L.iter()
                    .zip(G_factors[n..2 * n].iter())
                    .map(|(a_L_i, g)| a_L_i * g)
                    .chain(
                        b_R.iter()
                            .zip(H_factors[0..n].iter())
                            .map(|(b_R_i, h)| b_R_i * h),
                    ),
                G_R.iter().chain(H_L.iter()).copied(),
            ) + c_L * &Q;

            let R = StarkPoint::msm_authenticated_iter(
                a_R.iter()
                    .zip(G_factors[0..n].iter())
                    .map(|(a_R_i, g)| a_R_i * g)
                    .chain(
                        b_L.iter()
                            .zip(H_factors[n..2 * n].iter())
                            .map(|(b_L_i, h)| b_L_i * h),
                    ),
                G_L.iter().chain(H_R.iter()).copied(),
            ) + c_R * &Q;

            // Open the values before adding to the transcript
            // Otherwise, the parties will have inconsistent views of the transcript and
            // generate invalid secret shares of the challenge values
            let (L_open, R_open) = (L.open_authenticated(), R.open_authenticated());

            transcript.append_point(b"L", &L_open.value);
            transcript.append_point(b"R", &R_open.value);

            L_vec.push(L_open);
            R_vec.push(R_open);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = u.inverse();

            for i in 0..n {
                a_L[i] = &a_L[i] * &u + &u_inv * &a_R[i];
                b_L[i] = &b_L[i] * &u_inv + &u * &b_R[i];

                G_res.push(StarkPoint::msm_results(
                    &[&u_inv * &G_factors[i], &u * &G_factors[n + i]],
                    &[G_L[i], G_R[i]],
                ));
                H_res.push(StarkPoint::msm_results(
                    &[&u * &H_factors[i], &u_inv * &H_factors[n + i]],
                    &[H_L[i], H_R[i]],
                ));
            }

            a = a_L;
            b = b_L;
        }

        let mut G_res = &mut G_res[..];
        let mut H_res = &mut H_res[..];
        while n != 1 {
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G_res.split_at_mut(n);
            let (H_L, H_R) = H_res.split_at_mut(n);

            let c_L = authenticated_inner_product(a_L, b_R, fabric.clone());
            let c_R = authenticated_inner_product(a_R, b_L, fabric.clone());

            let L = StarkPointResult::msm_authenticated_iter(
                a_L.iter()
                    .chain(b_R.iter())
                    .chain(iter::once(&c_L))
                    .cloned(),
                G_R.iter().chain(H_L.iter()).chain(iter::once(&Q)).cloned(),
            );

            let R = StarkPointResult::msm_authenticated_iter(
                a_R.iter()
                    .chain(b_L.iter())
                    .chain(iter::once(&c_R))
                    .cloned(),
                G_L.iter().chain(H_R.iter()).chain(iter::once(&Q)).cloned(),
            );

            // Open the values before adding to the transcript
            // Otherwise, the parties will have inconsistent views of the transcript and
            // generate invalid secret shares of the challenge values
            let (L_open, R_open) = (L.open_authenticated(), R.open_authenticated());

            transcript.append_point(b"L", &L_open.value);
            transcript.append_point(b"R", &R_open.value);

            L_vec.push(L_open);
            R_vec.push(R_open);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = u.inverse();

            for i in 0..n {
                a_L[i] = &a_L[i] * &u + &u_inv * &a_R[i];
                b_L[i] = &b_L[i] * &u_inv + &u * &b_R[i];

                G_L[i] = StarkPointResult::msm_results(
                    &[u_inv.clone(), u.clone()],
                    &[G_L[i].clone(), G_R[i].clone()],
                );
                H_L[i] = StarkPointResult::msm_results(
                    &[u.clone(), u_inv.clone()],
                    &[H_L[i].clone(), H_R[i].clone()],
                );
            }

            a = a_L;
            b = b_L;
            G_res = G_L;
            H_res = H_L;
        }

        Ok(SharedInnerProductProof {
            L_vec,
            R_vec,
            a: a[0].clone(),
            b: b[0].clone(),
        })
    }

    /// Returns the size in bytes required to serialize the inner
    /// product proof.
    ///
    /// For vectors of length `n` the proof size is
    /// \\(32 \cdot (2\lg n+2)\\) bytes.
    pub fn serialized_size(&self) -> usize {
        (self.L_vec.len() * 2 + 2) * 32
    }

    /// Opens a shared proof
    ///
    /// Each party shares the values in their proof elements and computes the cleartext values from
    /// the set of additive shares
    ///
    /// The resulting type is `InnerProductProof` as the values are no longer secret shared
    pub async fn open(&self) -> Result<InnerProductProof, MultiproverError> {
        // Open the scalars (a, b)
        // The Ristretto points are already opened as a result of running the protocol
        let a = self
            .a
            .open_authenticated()
            .await
            .map_err(MultiproverError::Mpc)?;
        let b = self
            .b
            .open_authenticated()
            .await
            .map_err(MultiproverError::Mpc)?;

        let L_vec = join_all(self.L_vec.iter().cloned())
            .await
            .into_iter()
            .collect::<Result<Vec<_>, MpcError>>()
            .map_err(MultiproverError::Mpc)?;
        let R_vec = join_all(self.R_vec.iter().cloned())
            .await
            .into_iter()
            .collect::<Result<Vec<_>, MpcError>>()
            .map_err(MultiproverError::Mpc)?;

        Ok(InnerProductProof { L_vec, R_vec, a, b })
    }
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
#[allow(dead_code)]
pub fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
    let mut out = Scalar::zero();
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

/// Computes an inner product between two vectors of authenticated scalars
pub fn authenticated_inner_product(
    a: &[AuthenticatedScalarResult],
    b: &[AuthenticatedScalarResult],
    fabric: MpcFabric,
) -> AuthenticatedScalarResult {
    let mut out = fabric.zero_authenticated();
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out = out + &a[i] * &b[i];
    }
    out
}
