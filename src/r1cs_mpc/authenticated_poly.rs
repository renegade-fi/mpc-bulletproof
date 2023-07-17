#![deny(missing_docs)]
#![allow(non_snake_case)]
#![allow(dead_code)]

//! Groups the representation and arithmetic of polynomials over the field of
//! `AuthenticatedScalar`s.

extern crate alloc;

use core::panic;

use alloc::vec::Vec;
use mpc_stark::{
    algebra::{authenticated_scalar::AuthenticatedScalarResult, scalar::ScalarResult},
    MpcFabric,
};

/// Represents a degree-1 vector polynomial \\(\mathbf{a} + \mathbf{b} \cdot x\\).
pub struct AuthenticatedVecPoly1(
    pub Vec<AuthenticatedScalarResult>,
    pub Vec<AuthenticatedScalarResult>,
);

/// Represents a degree-3 vector polynomial
/// \\(\mathbf{a} + \mathbf{b} \cdot x + \mathbf{c} \cdot x^2 + \mathbf{d} \cdot x^3 \\).
#[cfg(feature = "multiprover")]
pub struct AuthenticatedVecPoly3(
    pub Vec<AuthenticatedScalarResult>,
    pub Vec<AuthenticatedScalarResult>,
    pub Vec<AuthenticatedScalarResult>,
    pub Vec<AuthenticatedScalarResult>,
);

/// Represents a degree-2 scalar polynomial \\(a + b \cdot x + c \cdot x^2\\)
pub struct AuthenticatedPoly2(
    pub AuthenticatedScalarResult,
    pub AuthenticatedScalarResult,
    pub AuthenticatedScalarResult,
);

/// Represents a degree-6 scalar polynomial, without the zeroth degree
/// \\(a \cdot x + b \cdot x^2 + c \cdot x^3 + d \cdot x^4 + e \cdot x^5 + f \cdot x^6\\)
#[allow(missing_docs)]
pub struct AuthenticatedPoly6 {
    pub t1: AuthenticatedScalarResult,
    pub t2: AuthenticatedScalarResult,
    pub t3: AuthenticatedScalarResult,
    pub t4: AuthenticatedScalarResult,
    pub t5: AuthenticatedScalarResult,
    pub t6: AuthenticatedScalarResult,
}

/// Provides an iterator over the powers of a `AuthenticatedScalarResult`.
///
/// This struct is created by the `exp_iter` function.
pub struct AuthenticatedScalarExp {
    x: AuthenticatedScalarResult,
    next_exp_x: AuthenticatedScalarResult,
}

/// Add two vectors of `AuthenticatedScalar`s.
pub fn add_vec(
    a: &[AuthenticatedScalarResult],
    b: &[AuthenticatedScalarResult],
) -> Vec<AuthenticatedScalarResult> {
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
pub fn authenticated_scalar_inner_product(
    a: &[AuthenticatedScalarResult],
    b: &[AuthenticatedScalarResult],
) -> AuthenticatedScalarResult {
    if a.len() != b.len() || a.is_empty() {
        panic!("invalid vector lengths for inner product");
    }

    // Start from one so that we can construct the type as AuthenticatedScalar
    // without access to the fabric. This simplifies the interface.
    let mut out = &a[0] * &b[0];
    for i in 1..a.len() {
        out = out + &a[i] * &b[i];
    }
    out
}

impl AuthenticatedVecPoly1 {
    /// Constructs the zero polynomial over the field of `AuthenticatedScalar`s represented
    /// as a degree 1 polynomial
    pub fn zero(n: usize, fabric: MpcFabric) -> Self {
        AuthenticatedVecPoly1(fabric.zeros_authenticated(n), fabric.zeros_authenticated(n))
    }

    /// Returns the inner product of two vectors of degree 1 polynomials
    pub fn inner_product(&self, rhs: &AuthenticatedVecPoly1) -> AuthenticatedPoly2 {
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
    pub fn eval(&self, x: AuthenticatedScalarResult) -> Vec<AuthenticatedScalarResult> {
        let n = self.0.len();
        (0..n)
            .map(|i| &self.0[i] + &x * &self.1[i])
            .collect::<Vec<AuthenticatedScalarResult>>()
    }
}

impl AuthenticatedVecPoly3 {
    /// Returns the zero polynomial over the field of `AuthenticatedScalar`s represented
    /// as a degree 3 polynomial
    pub fn zero(n: usize, fabric: MpcFabric) -> Self {
        AuthenticatedVecPoly3(
            fabric.zeros_authenticated(n),
            fabric.zeros_authenticated(n),
            fabric.zeros_authenticated(n),
            fabric.zeros_authenticated(n),
        )
    }

    /// Compute an inner product of `lhs`, `rhs` which have the property that:
    /// - `lhs.0` is zero;
    /// - `rhs.2` is zero;
    /// This is the case in the constraint system proof.
    pub fn special_inner_product(lhs: &Self, rhs: &Self) -> AuthenticatedPoly6 {
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

    /// Evaluates the polynomial at `x` for a public MPC value
    pub fn eval(&self, x: &ScalarResult) -> Vec<AuthenticatedScalarResult> {
        (0..self.0.len())
            .map(|i| &self.0[i] + x * (&self.1[i] + x * (&self.2[i] + x * &self.3[i])))
            .collect::<Vec<AuthenticatedScalarResult>>()
    }

    /// Evaluates the polynomial at `x`, for a share MPC value
    pub fn eval_authenticated(
        &self,
        x: &AuthenticatedScalarResult,
    ) -> Vec<AuthenticatedScalarResult> {
        (0..self.0.len())
            .map(|i| &self.0[i] + x * (&self.1[i] + x * (&self.2[i] + x * &self.3[i])))
            .collect::<Vec<AuthenticatedScalarResult>>()
    }
}

impl AuthenticatedPoly2 {
    /// Evaluates the polynomial at `x`
    pub fn eval(&self, x: &AuthenticatedScalarResult) -> AuthenticatedScalarResult {
        &self.0 + x * (&self.1 + x * &self.2)
    }
}

impl AuthenticatedPoly6 {
    /// Evaluates the polynomial at `x` which is a public MPC value
    pub fn eval(&self, x: &ScalarResult) -> AuthenticatedScalarResult {
        x * (&self.t1
            + x * (&self.t2 + x * (&self.t3 + x * (&self.t4 + x * (&self.t5 + x * &self.t6)))))
    }

    /// Evaluates the polynomial at `x` for an `AuthenticatedScalar` `x`
    pub fn eval_authenticated(&self, x: &AuthenticatedScalarResult) -> AuthenticatedScalarResult {
        x * (&self.t1
            + x * (&self.t2 + x * (&self.t3 + x * (&self.t4 + x * (&self.t5 + x * &self.t6)))))
    }
}

/// Raises `x` to the power `n` using binary exponentiation,
/// with (1 to 2)*lg(n) scalar multiplications.
/// TODO: a constant time version of this would be awfully similar to a Montgomery ladder.
pub fn authenticated_scalar_exp_vartime(
    x: &AuthenticatedScalarResult,
    mut n: u64,
    fabric: MpcFabric,
) -> AuthenticatedScalarResult {
    let mut result = fabric.one_authenticated();
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

/// Given `data` with `len >= 32`, return the first 32 bytes.
pub fn read32(data: &[u8]) -> [u8; 32] {
    let mut buf32 = [0u8; 32];
    buf32[..].copy_from_slice(&data[..32]);
    buf32
}

#[cfg(test)]
mod tests {
    use async_trait::async_trait;
    use mpc_stark::{
        algebra::scalar::Scalar,
        beaver::SharedValueSource,
        error::MpcNetworkError,
        network::{MpcNetwork, NetworkOutbound, NetworkPayload, PartyId},
        PARTY0,
    };

    use crate::inner_product_proof::inner_product;

    /// Mock Beaver source
    #[derive(Debug, Default)]
    pub struct DummySharedScalarSource;

    impl DummySharedScalarSource {
        pub fn new() -> Self {
            Self
        }
    }

    impl SharedValueSource for DummySharedScalarSource {
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
        fn party_id(&self) -> PartyId {
            PARTY0
        }

        async fn send_message(&mut self, _message: NetworkOutbound) -> Result<(), MpcNetworkError> {
            Ok(())
        }

        async fn receive_message(&mut self) -> Result<NetworkOutbound, MpcNetworkError> {
            Ok(NetworkOutbound {
                op_id: 0,
                payload: NetworkPayload::Scalar(Scalar::one()),
            })
        }

        async fn exchange_messages(
            &mut self,
            _message: NetworkOutbound,
        ) -> Result<NetworkOutbound, MpcNetworkError> {
            Ok(NetworkOutbound {
                op_id: 0,
                payload: NetworkPayload::Scalar(Scalar::one()),
            })
        }

        async fn close(&mut self) -> Result<(), MpcNetworkError> {
            Ok(())
        }
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
            result = result * x;
        }
        result
    }
}
