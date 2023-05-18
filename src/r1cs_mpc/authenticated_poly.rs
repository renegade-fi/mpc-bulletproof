#![deny(missing_docs)]
#![allow(non_snake_case)]
#![allow(dead_code)]

//! Groups the representation and arithmetic of polynomials over the field of
//! `AuthenticatedScalar`s.

extern crate alloc;

use core::panic;

use alloc::vec::Vec;
use clear_on_drop::clear::Clear;
use curve25519_dalek::scalar::Scalar;
use mpc_ristretto::authenticated_scalar::AuthenticatedScalar;
use mpc_ristretto::beaver::SharedValueSource;
use mpc_ristretto::network::MpcNetwork;

use super::mpc_prover::SharedMpcFabric;

/// Represents a degree-1 vector polynomial \\(\mathbf{a} + \mathbf{b} \cdot x\\).
pub struct AuthenticatedVecPoly1<N: MpcNetwork + Send, S: SharedValueSource<Scalar>>(
    pub Vec<AuthenticatedScalar<N, S>>,
    pub Vec<AuthenticatedScalar<N, S>>,
);

/// Represents a degree-3 vector polynomial
/// \\(\mathbf{a} + \mathbf{b} \cdot x + \mathbf{c} \cdot x^2 + \mathbf{d} \cdot x^3 \\).
#[cfg(feature = "multiprover")]
pub struct AuthenticatedVecPoly3<N: MpcNetwork + Send, S: SharedValueSource<Scalar>>(
    pub Vec<AuthenticatedScalar<N, S>>,
    pub Vec<AuthenticatedScalar<N, S>>,
    pub Vec<AuthenticatedScalar<N, S>>,
    pub Vec<AuthenticatedScalar<N, S>>,
);

/// Represents a degree-2 scalar polynomial \\(a + b \cdot x + c \cdot x^2\\)
pub struct AuthenticatedPoly2<N: MpcNetwork + Send, S: SharedValueSource<Scalar>>(
    pub AuthenticatedScalar<N, S>,
    pub AuthenticatedScalar<N, S>,
    pub AuthenticatedScalar<N, S>,
);

/// Represents a degree-6 scalar polynomial, without the zeroth degree
/// \\(a \cdot x + b \cdot x^2 + c \cdot x^3 + d \cdot x^4 + e \cdot x^5 + f \cdot x^6\\)
#[allow(missing_docs)]
pub struct AuthenticatedPoly6<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> {
    pub t1: AuthenticatedScalar<N, S>,
    pub t2: AuthenticatedScalar<N, S>,
    pub t3: AuthenticatedScalar<N, S>,
    pub t4: AuthenticatedScalar<N, S>,
    pub t5: AuthenticatedScalar<N, S>,
    pub t6: AuthenticatedScalar<N, S>,
}

/// Provides an iterator over the powers of a `AuthenticatedScalar<N, S>`.
///
/// This struct is created by the `exp_iter` function.
pub struct AuthenticatedScalarExp<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> {
    x: AuthenticatedScalar<N, S>,
    next_exp_x: AuthenticatedScalar<N, S>,
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Iterator for AuthenticatedScalarExp<N, S> {
    type Item = AuthenticatedScalar<N, S>;

    fn next(&mut self) -> Option<AuthenticatedScalar<N, S>> {
        let exp_x = self.next_exp_x.clone();
        self.next_exp_x = &self.next_exp_x * &self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn authenticated_exp_iter<N, S>(
    x: AuthenticatedScalar<N, S>,
    fabric: SharedMpcFabric<N, S>,
) -> AuthenticatedScalarExp<N, S>
where
    N: MpcNetwork + Send,
    S: SharedValueSource<Scalar>,
{
    let next_exp_x = fabric
        .as_ref()
        .borrow()
        .allocate_public_scalar(Scalar::one());

    AuthenticatedScalarExp { x, next_exp_x }
}

/// Add two vectors of `AuthenticatedScalar`s.
pub fn add_vec<N, S>(
    a: &[AuthenticatedScalar<N, S>],
    b: &[AuthenticatedScalar<N, S>],
) -> Vec<AuthenticatedScalar<N, S>>
where
    N: MpcNetwork + Send,
    S: SharedValueSource<Scalar>,
{
    if a.len() != b.len() {
        panic!("Invalid vector lengths for add_vec");
    }
    let mut out = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        out[i] = &a[i] + &b[i];
    }
    out
}

/// Compute the inner product of two vectors of `AuthenticatedScalar`s.
pub fn authenticated_scalar_inner_product<N, S>(
    a: &[AuthenticatedScalar<N, S>],
    b: &[AuthenticatedScalar<N, S>],
) -> AuthenticatedScalar<N, S>
where
    N: MpcNetwork + Send,
    S: SharedValueSource<Scalar>,
{
    if a.len() != b.len() || a.is_empty() {
        panic!("invalid vector lengths for inner product");
    }

    // Start from one so that we can construct the type as AuthenticatedScalar
    // without access to the fabric. This simplifies the interface.
    let mut out = &a[0] * &b[0];
    for i in 1..a.len() {
        out += &a[i] * &b[i];
    }
    out
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> AuthenticatedVecPoly1<N, S> {
    /// Constructs the zero polynomial over the field of `AuthenticatedScalar`s represented
    /// as a degree 1 polynomial
    pub fn zero(n: usize, fabric: SharedMpcFabric<N, S>) -> Self {
        let fabric_borrow = fabric.as_ref().borrow();
        AuthenticatedVecPoly1(
            fabric_borrow.allocate_zeros(n),
            fabric_borrow.allocate_zeros(n),
        )
    }

    /// Returns the inner product of two vectors of degree 1 polynomials
    pub fn inner_product(&self, rhs: &AuthenticatedVecPoly1<N, S>) -> AuthenticatedPoly2<N, S> {
        // Uses Karatsuba's method
        let l = self;
        let r = rhs;

        let t0 = authenticated_scalar_inner_product(&l.0, &r.0);
        let t2 = authenticated_scalar_inner_product(&l.1, &r.1);

        let l0_plus_l1 = add_vec(&l.0, &l.1);
        let r0_plus_r1 = add_vec(&r.0, &r.1);

        let t1 = authenticated_scalar_inner_product(&l0_plus_l1, &r0_plus_r1) - &t0 - &t2;

        AuthenticatedPoly2(t0, t1, t2)
    }

    /// Evaluates the polynomial at `x`
    pub fn eval(&self, x: AuthenticatedScalar<N, S>) -> Vec<AuthenticatedScalar<N, S>> {
        let n = self.0.len();
        (0..n)
            .map(|i| &self.0[i] + &x * &self.1[i])
            .collect::<Vec<AuthenticatedScalar<N, S>>>()
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> AuthenticatedVecPoly3<N, S> {
    /// Returns the zero polynomial over the field of `AuthenticatedScalar`s represented
    /// as a degree 3 polynomial
    pub fn zero(n: usize, fabric: SharedMpcFabric<N, S>) -> Self {
        let fabric_borrow = fabric.as_ref().borrow();
        AuthenticatedVecPoly3(
            fabric_borrow.allocate_zeros(n),
            fabric_borrow.allocate_zeros(n),
            fabric_borrow.allocate_zeros(n),
            fabric_borrow.allocate_zeros(n),
        )
    }

    /// Compute an inner product of `lhs`, `rhs` which have the property that:
    /// - `lhs.0` is zero;
    /// - `rhs.2` is zero;
    /// This is the case in the constraint system proof.
    pub fn special_inner_product(lhs: &Self, rhs: &Self) -> AuthenticatedPoly6<N, S> {
        // TODO: make checks that l_poly.0 and r_poly.2 are zero.

        let t1 = authenticated_scalar_inner_product(&lhs.1, &rhs.0);
        let t2 = authenticated_scalar_inner_product(&lhs.1, &rhs.1)
            + authenticated_scalar_inner_product(&lhs.2, &rhs.0);
        let t3 = authenticated_scalar_inner_product(&lhs.2, &rhs.1)
            + authenticated_scalar_inner_product(&lhs.3, &rhs.0);
        let t4 = authenticated_scalar_inner_product(&lhs.1, &rhs.3)
            + authenticated_scalar_inner_product(&lhs.3, &rhs.1);
        let t5 = authenticated_scalar_inner_product(&lhs.2, &rhs.3);
        let t6 = authenticated_scalar_inner_product(&lhs.3, &rhs.3);

        AuthenticatedPoly6 {
            t1,
            t2,
            t3,
            t4,
            t5,
            t6,
        }
    }

    /// Evaluates the polynomial at `x`
    pub fn eval(&self, x: &AuthenticatedScalar<N, S>) -> Vec<AuthenticatedScalar<N, S>> {
        (0..self.0.len())
            .map(|i| &self.0[i] + x * (&self.1[i] + x * (&self.2[i] + x * &self.3[i])))
            .collect::<Vec<AuthenticatedScalar<N, S>>>()
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> AuthenticatedPoly2<N, S> {
    /// Evaluates the polynomial at `x`
    pub fn eval(&self, x: &AuthenticatedScalar<N, S>) -> AuthenticatedScalar<N, S> {
        &self.0 + x * (&self.1 + x * &self.2)
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> AuthenticatedPoly6<N, S> {
    /// Evaluates the polynomial at `x`
    pub fn eval(&self, x: &AuthenticatedScalar<N, S>) -> AuthenticatedScalar<N, S> {
        x * (&self.t1
            + x * (&self.t2 + x * (&self.t3 + x * (&self.t4 + x * (&self.t5 + x * &self.t6)))))
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Drop for AuthenticatedVecPoly1<N, S> {
    fn drop(&mut self) {
        for e in self.0.iter_mut() {
            (&mut (*e)).clear();
        }
        for e in self.1.iter_mut() {
            (&mut (*e)).clear();
        }
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Drop for AuthenticatedPoly2<N, S> {
    fn drop(&mut self) {
        (&mut self.0).clear();
        (&mut self.1).clear();
        (&mut self.2).clear();
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Drop for AuthenticatedVecPoly3<N, S> {
    fn drop(&mut self) {
        for e in self.0.iter_mut() {
            (&mut (*e)).clear();
        }
        for e in self.1.iter_mut() {
            (&mut (*e)).clear();
        }
        for e in self.2.iter_mut() {
            (&mut (*e)).clear();
        }
        for e in self.3.iter_mut() {
            (&mut (*e)).clear();
        }
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Drop for AuthenticatedPoly6<N, S> {
    fn drop(&mut self) {
        (&mut self.t1).clear();
        (&mut self.t2).clear();
        (&mut self.t3).clear();
        (&mut self.t4).clear();
        (&mut self.t5).clear();
        (&mut self.t6).clear();
    }
}

/// Raises `x` to the power `n` using binary exponentiation,
/// with (1 to 2)*lg(n) scalar multiplications.
/// TODO: a consttime version of this would be awfully similar to a Montgomery ladder.
pub fn authenticated_scalar_exp_vartime<N, S>(
    x: &AuthenticatedScalar<N, S>,
    mut n: u64,
    fabric: SharedMpcFabric<N, S>,
) -> AuthenticatedScalar<N, S>
where
    N: MpcNetwork + Send,
    S: SharedValueSource<Scalar>,
{
    let mut result = fabric
        .as_ref()
        .borrow()
        .allocate_public_scalar(Scalar::one());
    let mut aux = x.clone(); // x, x^2, x^4, x^8, ...
    while n > 0 {
        let bit = n & 1;
        if bit == 1 {
            result = &aux * result;
        }
        n >>= 1;
        if n == 0 {
            break;
        }

        aux = &aux * &aux;
    }
    result
}

/// Takes the sum of all the powers of `x`, up to `n`
/// If `n` is a power of 2, it uses the efficient algorithm with `2*lg n` multiplications and additions.
/// If `n` is not a power of 2, it uses the slow algorithm with `n` multiplications and additions.
/// In the Bulletproofs case, all calls to `sum_of_powers` should have `n` as a power of 2.
pub fn authenticated_sum_of_powers<N, S>(
    x: &AuthenticatedScalar<N, S>,
    n: usize,
    fabric: SharedMpcFabric<N, S>,
) -> AuthenticatedScalar<N, S>
where
    N: MpcNetwork + Send,
    S: SharedValueSource<Scalar>,
{
    if !n.is_power_of_two() {
        return authenticated_sum_of_powers_slow(x, n, fabric);
    }
    if n == 0 || n == 1 {
        return fabric.as_ref().borrow().allocate_public_u64(n as u64);
    }
    let mut m = n;
    let mut result = Scalar::one() + x;
    let mut factor = x.clone();
    while m > 2 {
        factor = &factor * &factor;
        result = &result + &factor * &result;
        m /= 2;
    }
    result
}

// takes the sum of all of the powers of x, up to n
fn authenticated_sum_of_powers_slow<N, S>(
    x: &AuthenticatedScalar<N, S>,
    n: usize,
    fabric: SharedMpcFabric<N, S>,
) -> AuthenticatedScalar<N, S>
where
    N: MpcNetwork + Send,
    S: SharedValueSource<Scalar>,
{
    if n == 0 {
        return fabric.as_ref().borrow().allocate_public_u64(0);
    }

    authenticated_exp_iter(x.clone(), fabric).take(n).sum()
}

/// Given `data` with `len >= 32`, return the first 32 bytes.
pub fn read32(data: &[u8]) -> [u8; 32] {
    let mut buf32 = [0u8; 32];
    buf32[..].copy_from_slice(&data[..32]);
    buf32
}

#[cfg(test)]
mod tests {
    use core::cell::RefCell;

    use alloc::rc::Rc;
    use async_trait::async_trait;
    use curve25519_dalek::ristretto::RistrettoPoint;
    use mpc_ristretto::{error::MpcNetworkError, fabric::AuthenticatedMpcFabric};

    use crate::inner_product_proof::inner_product;

    use super::*;

    /// Mock Beaver source
    #[derive(Debug, Default)]
    pub struct DummySharedScalarSource;

    impl DummySharedScalarSource {
        pub fn new() -> Self {
            Self
        }
    }

    impl SharedValueSource<Scalar> for DummySharedScalarSource {
        fn next_shared_bit(&mut self) -> Scalar {
            Scalar::one()
        }

        fn next_shared_value(&mut self) -> Scalar {
            Scalar::one()
        }

        fn next_shared_inverse_pair(&mut self) -> (Scalar, Scalar) {
            (Scalar::one(), Scalar::one())
        }

        fn next_triplet(&mut self) -> (Scalar, Scalar, Scalar) {
            (Scalar::one(), Scalar::one(), Scalar::one())
        }
    }

    /// Mock MPC Network
    #[derive(Clone, Debug)]
    pub struct DummyMpcNetwork;
    impl DummyMpcNetwork {
        fn new() -> Self {
            Self
        }
    }

    #[async_trait]
    impl MpcNetwork for DummyMpcNetwork {
        /// Always return king
        fn party_id(&self) -> u64 {
            0
        }

        async fn send_bytes(&mut self, _: &[u8]) -> Result<(), MpcNetworkError> {
            Ok(())
        }

        async fn receive_bytes(
            &mut self,
            _num_expected: usize,
        ) -> Result<Vec<u8>, MpcNetworkError> {
            unimplemented!("not used in testing")
        }

        async fn send_scalars(&mut self, _: &[Scalar]) -> Result<(), MpcNetworkError> {
            Ok(())
        }

        async fn receive_scalars(&mut self, _: usize) -> Result<Vec<Scalar>, MpcNetworkError> {
            Ok(vec![])
        }

        async fn broadcast_points(
            &mut self,
            points: &[RistrettoPoint],
        ) -> Result<Vec<RistrettoPoint>, MpcNetworkError> {
            Ok(points.to_vec())
        }

        async fn send_points(&mut self, _: &[RistrettoPoint]) -> Result<(), MpcNetworkError> {
            Ok(())
        }

        async fn receive_points(
            &mut self,
            _: usize,
        ) -> Result<Vec<RistrettoPoint>, MpcNetworkError> {
            Ok(vec![])
        }

        async fn broadcast_scalars(
            &mut self,
            scalars: &[Scalar],
        ) -> Result<Vec<Scalar>, MpcNetworkError> {
            Ok(scalars.to_vec())
        }

        async fn close(&mut self) -> Result<(), MpcNetworkError> {
            Ok(())
        }
    }

    fn create_mock_fabric() -> SharedMpcFabric<DummyMpcNetwork, DummySharedScalarSource> {
        Rc::new(RefCell::new(AuthenticatedMpcFabric::new_with_network(
            0,
            Rc::new(RefCell::new(DummyMpcNetwork::new())),
            Rc::new(RefCell::new(DummySharedScalarSource::new())),
        )))
    }

    #[test]
    fn exp_2_is_powers_of_2() {
        let mock_fabric = create_mock_fabric();
        let exp_2 = authenticated_exp_iter(
            mock_fabric.as_ref().borrow().allocate_public_u64(2),
            mock_fabric.clone(),
        )
        .take(4)
        .collect::<Vec<_>>();

        assert_eq!(exp_2[0].to_scalar(), Scalar::from(1u64));
        assert_eq!(exp_2[1].to_scalar(), Scalar::from(2u64));
        assert_eq!(exp_2[2].to_scalar(), Scalar::from(4u64));
        assert_eq!(exp_2[3].to_scalar(), Scalar::from(8u64));
    }

    #[test]
    fn test_inner_product() {
        let a = vec![
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
        ];
        let b = vec![
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(5u64),
        ];
        assert_eq!(Scalar::from(40u64), inner_product(&a, &b));
    }

    /// Raises `x` to the power `n`.
    fn scalar_exp_vartime_slow(x: &Scalar, n: u64) -> Scalar {
        let mut result = Scalar::one();
        for _ in 0..n {
            result *= x;
        }
        result
    }

    #[test]
    fn test_scalar_exp() {
        let mock_fabric = create_mock_fabric();
        let x_scalar = Scalar::from_bits(
            *b"\x84\xfc\xbcOx\x12\xa0\x06\xd7\x91\xd9z:'\xdd\x1e!CE\xf7\xb1\xb9Vz\x810sD\x96\x85\xb5\x07",
        );
        let x = mock_fabric
            .as_ref()
            .borrow()
            .allocate_public_scalar(x_scalar);

        assert_eq!(
            authenticated_scalar_exp_vartime(&x, 0, mock_fabric.clone()).to_scalar(),
            Scalar::one()
        );
        assert_eq!(
            authenticated_scalar_exp_vartime(&x, 1, mock_fabric.clone()).to_scalar(),
            x_scalar
        );
        assert_eq!(
            authenticated_scalar_exp_vartime(&x, 2, mock_fabric.clone()).to_scalar(),
            x_scalar * x_scalar
        );
        assert_eq!(
            authenticated_scalar_exp_vartime(&x, 3, mock_fabric.clone()).to_scalar(),
            x_scalar * x_scalar * x_scalar
        );
        assert_eq!(
            authenticated_scalar_exp_vartime(&x, 4, mock_fabric.clone()).to_scalar(),
            x_scalar * x_scalar * x_scalar * x_scalar
        );
        assert_eq!(
            authenticated_scalar_exp_vartime(&x, 5, mock_fabric.clone()).to_scalar(),
            x_scalar * x_scalar * x_scalar * x_scalar * x_scalar
        );
        assert_eq!(
            authenticated_scalar_exp_vartime(&x, 64, mock_fabric.clone()).to_scalar(),
            scalar_exp_vartime_slow(&x_scalar, 64)
        );
        assert_eq!(
            authenticated_scalar_exp_vartime(&x, 0b11001010, mock_fabric).to_scalar(),
            scalar_exp_vartime_slow(&x_scalar, 0b11001010)
        );
    }

    #[test]
    fn test_authenticated_sum_of_powers() {
        let mock_fabric = create_mock_fabric();
        let x = mock_fabric.as_ref().borrow().allocate_public_u64(10u64);
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 0, mock_fabric.clone()),
            authenticated_sum_of_powers(&x, 0, mock_fabric.clone())
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 1, mock_fabric.clone()),
            authenticated_sum_of_powers(&x, 1, mock_fabric.clone())
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 2, mock_fabric.clone()),
            authenticated_sum_of_powers(&x, 2, mock_fabric.clone())
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 4, mock_fabric.clone()),
            authenticated_sum_of_powers(&x, 4, mock_fabric.clone())
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 8, mock_fabric.clone()),
            authenticated_sum_of_powers(&x, 8, mock_fabric.clone())
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 16, mock_fabric.clone()),
            authenticated_sum_of_powers(&x, 16, mock_fabric.clone())
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 32, mock_fabric.clone()),
            authenticated_sum_of_powers(&x, 32, mock_fabric.clone())
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 64, mock_fabric.clone()),
            authenticated_sum_of_powers(&x, 64, mock_fabric)
        );
    }

    #[test]
    fn test_sum_of_powers_slow() {
        let mock_fabric = create_mock_fabric();
        let x = mock_fabric.as_ref().borrow().allocate_public_u64(10u64);
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 0, mock_fabric.clone()).to_scalar(),
            Scalar::zero()
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 1, mock_fabric.clone()).to_scalar(),
            Scalar::one()
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 2, mock_fabric.clone()).to_scalar(),
            Scalar::from(11u64)
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 3, mock_fabric.clone()).to_scalar(),
            Scalar::from(111u64)
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 4, mock_fabric.clone()).to_scalar(),
            Scalar::from(1111u64)
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 5, mock_fabric.clone()).to_scalar(),
            Scalar::from(11111u64)
        );
        assert_eq!(
            authenticated_sum_of_powers_slow(&x, 6, mock_fabric).to_scalar(),
            Scalar::from(111111u64)
        );
    }

    #[test]
    fn vec_of_scalars_clear_on_drop() {
        let mut v = vec![Scalar::from(24u64), Scalar::from(42u64)];

        for e in v.iter_mut() {
            e.clear();
        }

        fn flat_slice<T>(x: &[T]) -> &[u8] {
            use core::mem;
            use core::slice;

            unsafe { slice::from_raw_parts(x.as_ptr() as *const u8, mem::size_of_val(x)) }
        }

        assert_eq!(flat_slice(v.as_slice()), &[0u8; 64][..]);
        assert_eq!(v[0], Scalar::zero());
        assert_eq!(v[1], Scalar::zero());
    }

    #[test]
    fn tuple_of_scalars_clear_on_drop() {
        let mock_fabric = create_mock_fabric();
        let mut v = AuthenticatedPoly2(
            mock_fabric.as_ref().borrow().allocate_public_u64(24u64),
            mock_fabric.as_ref().borrow().allocate_public_u64(42u64),
            mock_fabric.as_ref().borrow().allocate_public_u64(255u64),
        );

        (&mut v.0).clear();
        (&mut v.1).clear();
        (&mut v.2).clear();

        assert_eq!(v.0.to_scalar(), Scalar::zero());
        assert_eq!(v.1.to_scalar(), Scalar::zero());
        assert_eq!(v.2.to_scalar(), Scalar::zero());
    }
}
