//! Groups the implementation of inner product proofs over an authenticated
//! scalar field

#![allow(non_snake_case)]
#![doc = include_str!("../../docs/inner-product-protocol.md")]

extern crate alloc;

use alloc::vec::Vec;
use mpc_ristretto::authenticated_ristretto::{
    AuthenticatedCompressedRistretto, AuthenticatedRistretto,
};
use mpc_ristretto::authenticated_scalar::AuthenticatedScalar;
use mpc_ristretto::beaver::SharedValueSource;
use mpc_ristretto::network::MpcNetwork;

use core::iter;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

use super::mpc_prover::SharedMpcFabric;

use crate::transcript::TranscriptProtocol;

/// An inner product proof that is secret shared between multiple proving parties.
///
/// This type does not include a verifier implementation; verification should happen
/// via the standard Bulletproof verifier defined in the parent module.
#[derive(Clone, Debug)]
pub struct SharedInnerProductProof<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> {
    pub(crate) L_vec: Vec<AuthenticatedCompressedRistretto<N, S>>,
    pub(crate) R_vec: Vec<AuthenticatedCompressedRistretto<N, S>>,
    pub(crate) a: AuthenticatedScalar<N, S>,
    pub(crate) b: AuthenticatedScalar<N, S>,
}

#[allow(clippy::too_many_arguments)]
impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> SharedInnerProductProof<N, S> {
    /// Create an inner-product proof.
    ///
    /// The proof is created with respect to the bases \\(G\\), \\(H'\\),
    /// where \\(H'\_i = H\_i \cdot \texttt{Hprime\\_factors}\_i\\).
    ///
    /// The lengths of the vectors must all be the same, and must all be
    /// either 0 or a power of 2.
    pub fn create(
        transcript: &mut Transcript,
        Q: &AuthenticatedRistretto<N, S>,
        G_factors: &[Scalar],
        H_factors: &[Scalar],
        mut G_vec: Vec<AuthenticatedRistretto<N, S>>,
        mut H_vec: Vec<AuthenticatedRistretto<N, S>>,
        mut a_vec: Vec<AuthenticatedScalar<N, S>>,
        mut b_vec: Vec<AuthenticatedScalar<N, S>>,
        fabric: SharedMpcFabric<N, S>,
    ) -> SharedInnerProductProof<N, S> {
        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
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

        // If it's the first iteration, unroll the Hprime = H*y_inv scalar mults
        // into multiscalar muls, for performance.
        if n != 1 {
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = authenticated_inner_product(a_L, b_R, fabric.clone());
            let c_R = authenticated_inner_product(a_R, b_L, fabric.clone());

            let L = AuthenticatedRistretto::multiscalar_mul(
                a_L.iter()
                    .zip(G_factors[n..2 * n].iter())
                    .map(|(a_L_i, g)| a_L_i * *g)
                    .chain(
                        b_R.iter()
                            .zip(H_factors[0..n].iter())
                            .map(|(b_R_i, h)| b_R_i * *h),
                    )
                    .chain(iter::once(c_L)),
                G_R.iter().chain(H_L.iter()).chain(iter::once(Q)),
            )
            .compress();

            let R = AuthenticatedRistretto::multiscalar_mul(
                a_R.iter()
                    .zip(G_factors[0..n].iter())
                    .map(|(a_R_i, g)| a_R_i * *g)
                    .chain(
                        b_L.iter()
                            .zip(H_factors[n..2 * n].iter())
                            .map(|(b_L_i, h)| b_L_i * *h),
                    )
                    .chain(iter::once(c_R)),
                G_L.iter().chain(H_R.iter()).chain(iter::once(Q)),
            )
            .compress();

            transcript.append_point(b"L", &L.value());
            transcript.append_point(b"R", &R.value());

            L_vec.push(L);
            R_vec.push(R);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = u.invert();

            for i in 0..n {
                a_L[i] = &a_L[i] * u + u_inv * &a_R[i];
                b_L[i] = &b_L[i] * u_inv + u * &b_R[i];

                // Allocate the points as network values before performing MSM
                let authenticated_G_coefficients = [u_inv * G_factors[i], u * G_factors[n + i]]
                    .iter()
                    .map(|value| fabric.as_ref().borrow().allocate_public_scalar(*value))
                    .collect::<Vec<_>>();

                let authenticated_H_coefficients = [u * H_factors[i], u_inv * H_factors[n + i]]
                    .iter()
                    .map(|value| fabric.as_ref().borrow().allocate_public_scalar(*value))
                    .collect::<Vec<_>>();

                G_L[i] = AuthenticatedRistretto::multiscalar_mul(
                    authenticated_G_coefficients,
                    [&G_L[i], &G_R[i]],
                );
                H_L[i] = AuthenticatedRistretto::multiscalar_mul(
                    authenticated_H_coefficients,
                    [&H_L[i], &H_R[i]],
                )
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        while n != 1 {
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = authenticated_inner_product(a_L, b_R, fabric.clone());
            let c_R = authenticated_inner_product(a_R, b_L, fabric.clone());

            let L = AuthenticatedRistretto::multiscalar_mul(
                a_L.iter().chain(b_R.iter()).chain(iter::once(&c_L)),
                G_R.iter().chain(H_L.iter()).chain(iter::once(Q)),
            )
            .compress();

            let R = AuthenticatedRistretto::multiscalar_mul(
                a_R.iter().chain(b_L.iter()).chain(iter::once(&c_R)),
                G_L.iter().chain(H_R.iter()).chain(iter::once(Q)),
            )
            .compress();

            transcript.append_point(b"L", &L.value());
            transcript.append_point(b"R", &R.value());

            L_vec.push(L);
            R_vec.push(R);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = u.invert();

            let authenticated_G_factors: &[AuthenticatedScalar<N, S>] = &[u_inv, u]
                .iter()
                .map(|value| fabric.as_ref().borrow().allocate_public_scalar(*value))
                .collect::<Vec<_>>();
            let authenticated_H_factors: &[AuthenticatedScalar<N, S>] = &[u, u_inv]
                .iter()
                .map(|value| fabric.as_ref().borrow().allocate_public_scalar(*value))
                .collect::<Vec<_>>();

            for i in 0..n {
                a_L[i] = &a_L[i] * u + u_inv * &a_R[i];
                b_L[i] = &b_L[i] * u_inv + u * &b_R[i];

                G_L[i] = AuthenticatedRistretto::multiscalar_mul(
                    authenticated_G_factors,
                    [&G_L[i], &G_R[i]],
                );
                H_L[i] = AuthenticatedRistretto::multiscalar_mul(
                    authenticated_H_factors,
                    [&H_L[i], &H_R[i]],
                );
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        SharedInnerProductProof {
            L_vec,
            R_vec,
            a: a[0].clone(),
            b: b[0].clone(),
        }
    }

    /// Returns the size in bytes required to serialize the inner
    /// product proof.
    ///
    /// For vectors of length `n` the proof size is
    /// \\(32 \cdot (2\lg n+2)\\) bytes.
    pub fn serialized_size(&self) -> usize {
        (self.L_vec.len() * 2 + 2) * 32
    }

    /// Serializes the proof into a byte array of \\(2n+2\\) 32-byte elements.
    /// The layout of the inner product proof is:
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0, R_0 \dots, L_{n-1}, R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    #[allow(dead_code)]
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        for (l, r) in self.L_vec.iter().zip(self.R_vec.iter()) {
            buf.extend_from_slice(l.as_bytes());
            buf.extend_from_slice(r.as_bytes());
        }
        buf.extend_from_slice(self.a.as_bytes());
        buf.extend_from_slice(self.b.as_bytes());
        buf
    }
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
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
pub fn authenticated_inner_product<N, S>(
    a: &[AuthenticatedScalar<N, S>],
    b: &[AuthenticatedScalar<N, S>],
    fabric: SharedMpcFabric<N, S>,
) -> AuthenticatedScalar<N, S>
where
    N: MpcNetwork + Send,
    S: SharedValueSource<Scalar>,
{
    let mut out = fabric.as_ref().borrow().allocate_public_u64(0);
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += &a[i] * &b[i];
    }
    out
}
