//! The `generators` module contains API for producing a
//! set of generators for a rangeproof.

#![allow(non_snake_case)]
#![deny(missing_docs)]

extern crate alloc;

use alloc::vec::Vec;
use merlin::{keccak256, pad_label};
use mpc_stark::algebra::authenticated_scalar::AuthenticatedScalarResult;
use mpc_stark::algebra::authenticated_stark_point::AuthenticatedStarkPointResult;
use mpc_stark::algebra::scalar::Scalar;
use mpc_stark::algebra::scalar::ScalarResult;
use mpc_stark::algebra::stark_curve::StarkPoint;
use mpc_stark::algebra::stark_curve::StarkPointResult;
use mpc_stark::algebra::stark_curve::STARK_POINT_BYTES;

/// Represents a pair of base points for Pedersen commitments.
///
/// The Bulletproofs implementation and API is designed to support
/// pluggable bases for Pedersen commitments, so that the choice of
/// bases is not hard-coded.
///
/// The default generators are:
///
/// * `B`: the `ristretto255` basepoint;
/// * `B_blinding`: the result of `ristretto255` SHA3-512
/// hash-to-group on input `B_bytes`.
#[derive(Copy, Clone)]
pub struct PedersenGens {
    /// Base for the committed value
    pub B: StarkPoint,
    /// Base for the blinding factor
    pub B_blinding: StarkPoint,
}

impl PedersenGens {
    /// Creates a Pedersen commitment using the value scalar and a blinding factor.
    pub fn commit(&self, value: Scalar, blinder: Scalar) -> StarkPoint {
        self.B * value + self.B_blinding * blinder
    }

    /// Creates a Pedersen commitment using the value scalar and a blinding factor represented
    /// as results in a computation graph
    pub fn commit_result(&self, value: &ScalarResult, blinder: &ScalarResult) -> StarkPointResult {
        self.B * value + self.B_blinding * blinder
    }

    /// Creates a Pedersen commitment using a shared scalar value and blinding factor.
    pub fn commit_shared(
        &self,
        value: &AuthenticatedScalarResult,
        blinding: &AuthenticatedScalarResult,
    ) -> AuthenticatedStarkPointResult {
        value * self.B + blinding * self.B_blinding
    }
}

impl Default for PedersenGens {
    fn default() -> Self {
        // We use the Stark curve's basepoint directly for both group generators as
        // in the original implementation over the Ristretto curve:
        //  https://github.com/dalek-cryptography/bulletproofs/blob/main/src/generators.rs#L44
        PedersenGens {
            B: StarkPoint::generator(),
            B_blinding: StarkPoint::generator(),
        }
    }
}

/// The `GeneratorsChain` creates an arbitrary-long sequence of
/// orthogonal generators.  The sequence can be deterministically
/// produced starting with an arbitrary point.
struct GeneratorsChain {
    state: [u8; 32],
}

impl GeneratorsChain {
    /// Creates a chain of generators, determined by the hash of `label`.
    fn new(label: &[u8]) -> Self {
        let mut state = [0_u8; 32];
        let input = pad_label([b"GeneratorsChain", label].concat().as_slice());

        keccak256(&input, &mut state);

        GeneratorsChain { state }
    }

    /// Advances the reader n times, squeezing and discarding
    /// the result.
    fn fast_forward(mut self, n: usize) -> Self {
        for _ in 0..n {
            let mut state = [0_u8; 32];
            keccak256(&self.state, &mut state);
            self.state = state;
        }
        self
    }
}

impl Default for GeneratorsChain {
    fn default() -> Self {
        Self::new(&[])
    }
}

impl Iterator for GeneratorsChain {
    type Item = StarkPoint;

    fn next(&mut self) -> Option<Self::Item> {
        let mut low_u256 = [0u8; STARK_POINT_BYTES];
        keccak256(&self.state, &mut low_u256);
        self.state.copy_from_slice(&low_u256);

        // Samples a uniformly random point on the curve in a manner that is consistent with the
        // Cairo implementation. Namely, convert the uniform bytes to a scalar field element, and
        // multiply by the generator point.
        // Examples of other such hash-to-curve schemes that do not hide the scalar multiple:
        // https://eprint.iacr.org/2009/226.pdf and https://link.springer.com/chapter/10.1007/978-3-642-14623-7_13
        let scalar = Scalar::from_uniform_bytes(low_u256);
        Some(scalar * StarkPoint::generator())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// The `BulletproofGens` struct contains all the generators needed
/// for aggregating up to `m` range proofs of up to `n` bits each.
///
/// # Extensible Generator Generation
///
/// Instead of constructing a single vector of size `m*n`, as
/// described in the Bulletproofs paper, we construct each party's
/// generators separately.
///
/// To construct an arbitrary-length chain of generators, we apply
/// SHAKE256 to a domain separator label, and feed each 64 bytes of
/// XOF output into the `ristretto255` hash-to-group function.
/// Each of the `m` parties' generators are constructed using a
/// different domain separation label, and proving and verification
/// uses the first `n` elements of the arbitrary-length chain.
///
/// This means that the aggregation size (number of
/// parties) is orthogonal to the rangeproof size (number of bits),
/// and allows using the same `BulletproofGens` object for different
/// proving parameters.
///
/// This construction is also forward-compatible with constraint
/// system proofs, which use a much larger slice of the generator
/// chain, and even forward-compatible to multiparty aggregation of
/// constraint system proofs, since the generators are namespaced by
/// their party index.
#[derive(Clone)]
pub struct BulletproofGens {
    /// The maximum number of usable generators for each party.
    pub gens_capacity: usize,
    /// Number of values or parties
    pub party_capacity: usize,
    /// Precomputed \\(\mathbf G\\) generators for each party.
    G_vec: Vec<Vec<StarkPoint>>,
    /// Precomputed \\(\mathbf H\\) generators for each party.
    H_vec: Vec<Vec<StarkPoint>>,
}

impl BulletproofGens {
    /// Create a new `BulletproofGens` object.
    ///
    /// # Inputs
    ///
    /// * `gens_capacity` is the number of generators to precompute
    ///    for each party.  For rangeproofs, it is sufficient to pass
    ///    `64`, the maximum bitsize of the rangeproofs.  For circuit
    ///    proofs, the capacity must be greater than the number of
    ///    multipliers, rounded up to the next power of two.
    ///
    /// * `party_capacity` is the maximum number of parties that can
    ///    produce an aggregated proof.
    pub fn new(gens_capacity: usize, party_capacity: usize) -> Self {
        let mut gens = BulletproofGens {
            gens_capacity: 0,
            party_capacity,
            G_vec: (0..party_capacity).map(|_| Vec::new()).collect(),
            H_vec: (0..party_capacity).map(|_| Vec::new()).collect(),
        };
        gens.increase_capacity(gens_capacity);
        gens
    }

    /// Returns j-th share of generators, with an appropriate
    /// slice of vectors G and H for the j-th range proof.
    pub fn share(&self, j: usize) -> BulletproofGensShare<'_> {
        BulletproofGensShare {
            gens: self,
            share: j,
        }
    }

    /// Returns a view of the generator chain that allocates generators
    /// as public curve points within an MPC network
    pub fn as_mpc_values(&self) -> AuthenticatedBulletproofGens {
        AuthenticatedBulletproofGens { gens: self }
    }

    /// Increases the generators' capacity to the amount specified.
    /// If less than or equal to the current capacity, does nothing.
    pub fn increase_capacity(&mut self, new_capacity: usize) {
        use byteorder::{ByteOrder, LittleEndian};

        if self.gens_capacity >= new_capacity {
            return;
        }

        for i in 0..self.party_capacity {
            let party_index = i as u32;
            let mut label = [b'G', 0, 0, 0, 0];
            LittleEndian::write_u32(&mut label[1..5], party_index);
            self.G_vec[i].extend(
                &mut GeneratorsChain::new(&label)
                    .fast_forward(self.gens_capacity)
                    .take(new_capacity - self.gens_capacity),
            );

            label[0] = b'H';
            self.H_vec[i].extend(
                &mut GeneratorsChain::new(&label)
                    .fast_forward(self.gens_capacity)
                    .take(new_capacity - self.gens_capacity),
            );
        }
        self.gens_capacity = new_capacity;
    }

    /// Return an iterator over the aggregation of the parties' G generators with given size `n`.
    #[cfg(test)]
    pub(crate) fn G(&self, n: usize, m: usize) -> impl Iterator<Item = &StarkPoint> {
        AggregatedGensIter {
            n,
            m,
            array: &self.G_vec,
            party_idx: 0,
            gen_idx: 0,
        }
    }

    /// Return an iterator over the aggregation of the parties' H generators with given size `n`.
    #[cfg(test)]
    pub(crate) fn H(&self, n: usize, m: usize) -> impl Iterator<Item = &StarkPoint> {
        AggregatedGensIter {
            n,
            m,
            array: &self.H_vec,
            party_idx: 0,
            gen_idx: 0,
        }
    }
}

struct AggregatedGensIter<'a> {
    array: &'a Vec<Vec<StarkPoint>>,
    n: usize,
    m: usize,
    party_idx: usize,
    gen_idx: usize,
}

impl<'a> Iterator for AggregatedGensIter<'a> {
    type Item = &'a StarkPoint;

    fn next(&mut self) -> Option<Self::Item> {
        if self.gen_idx >= self.n {
            self.gen_idx = 0;
            self.party_idx += 1;
        }

        if self.party_idx >= self.m {
            None
        } else {
            let cur_gen = self.gen_idx;
            self.gen_idx += 1;
            Some(&self.array[self.party_idx][cur_gen])
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.n * (self.m - self.party_idx) - self.gen_idx;
        (size, Some(size))
    }
}

/// Represents a view of the generators used by a specific party in an
/// aggregated proof.
///
/// The `BulletproofGens` struct represents generators for an aggregated
/// range proof `m` proofs of `n` bits each; the `BulletproofGensShare`
/// provides a view of the generators for one of the `m` parties' shares.
///
/// The `BulletproofGensShare` is produced by [`BulletproofGens::share()`].
#[derive(Copy, Clone)]
pub struct BulletproofGensShare<'a> {
    /// The parent object that this is a view into
    gens: &'a BulletproofGens,
    /// Which share we are
    share: usize,
}

impl<'a> BulletproofGensShare<'a> {
    /// Return an iterator over this party's G generators with given size `n`.
    pub fn G(&self, n: usize) -> impl Iterator<Item = &'a StarkPoint> {
        self.gens.G_vec[self.share].iter().take(n)
    }

    /// Return an iterator over this party's H generators with given size `n`.
    pub fn H(&self, n: usize) -> impl Iterator<Item = &'a StarkPoint> {
        self.gens.H_vec[self.share].iter().take(n)
    }
}

/// Represents a view of the generator as a series of public `AuthenticatedRistretto`s
///
/// This allows for the generators to be used more easily in algebraic expressions
/// with other network allocated values.
#[derive(Clone)]
pub struct AuthenticatedBulletproofGens<'a> {
    /// The parent object that this is a view into
    gens: &'a BulletproofGens,
}

impl<'a> AuthenticatedBulletproofGens<'a> {
    /// Return an iterator over G generators viewed as `AuthenticatedRistretto`s with given size `n`.
    pub fn G(&self, n: usize) -> impl Iterator<Item = &'a StarkPoint> {
        // It is necessary to materialize the mapping via collect to release the borrow on
        // the mpc fabric that is leased in the map closure.
        self.gens.G_vec[0].iter().take(n)
    }

    /// Return an iterator over H generators viewed as `AuthenticatedRistretto`s with given size `n`.
    pub(crate) fn H(&self, n: usize) -> impl Iterator<Item = &'a StarkPoint> {
        // It is necessary to materialize the mapping via collect to release the borrow on
        // the mpc fabric that is leased in the map closure.
        self.gens.H_vec[0].iter().take(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aggregated_gens_iter_matches_flat_map() {
        let gens = BulletproofGens::new(64, 8);

        let helper = |n: usize, m: usize| {
            let agg_G: Vec<StarkPoint> = gens.G(n, m).cloned().collect();
            let flat_G: Vec<StarkPoint> = gens
                .G_vec
                .iter()
                .take(m)
                .flat_map(move |G_j| G_j.iter().take(n))
                .cloned()
                .collect();

            let agg_H: Vec<StarkPoint> = gens.H(n, m).cloned().collect();
            let flat_H: Vec<StarkPoint> = gens
                .H_vec
                .iter()
                .take(m)
                .flat_map(move |H_j| H_j.iter().take(n))
                .cloned()
                .collect();

            assert_eq!(agg_G, flat_G);
            assert_eq!(agg_H, flat_H);
        };

        helper(64, 8);
        helper(64, 4);
        helper(64, 2);
        helper(64, 1);
        helper(32, 8);
        helper(32, 4);
        helper(32, 2);
        helper(32, 1);
        helper(16, 8);
        helper(16, 4);
        helper(16, 2);
        helper(16, 1);
    }

    #[test]
    fn resizing_small_gens_matches_creating_bigger_gens() {
        let gens = BulletproofGens::new(64, 8);

        let mut gen_resized = BulletproofGens::new(32, 8);
        gen_resized.increase_capacity(64);

        let helper = |n: usize, m: usize| {
            let gens_G: Vec<StarkPoint> = gens.G(n, m).cloned().collect();
            let gens_H: Vec<StarkPoint> = gens.H(n, m).cloned().collect();

            let resized_G: Vec<StarkPoint> = gen_resized.G(n, m).cloned().collect();
            let resized_H: Vec<StarkPoint> = gen_resized.H(n, m).cloned().collect();

            assert_eq!(gens_G, resized_G);
            assert_eq!(gens_H, resized_H);
        };

        helper(64, 8);
        helper(32, 8);
        helper(16, 8);
    }
}
