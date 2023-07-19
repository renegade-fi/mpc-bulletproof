#![allow(non_snake_case)]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use mpc_stark::{
    algebra::scalar::{Scalar, ScalarResult},
    MpcFabric,
};

use crate::inner_product_proof::inner_product;

/// Represents a degree-1 vector polynomial \\(\mathbf{a} + \mathbf{b} \cdot x\\).
pub struct VecPoly1(pub Vec<Scalar>, pub Vec<Scalar>);

/// Represents a degree-3 vector polynomial
/// \\(\mathbf{a} + \mathbf{b} \cdot x + \mathbf{c} \cdot x^2 + \mathbf{d} \cdot x^3 \\).
#[cfg(feature = "multiprover")]
pub struct VecPoly3(
    pub Vec<Scalar>,
    pub Vec<Scalar>,
    pub Vec<Scalar>,
    pub Vec<Scalar>,
);

/// Represents a degree-2 scalar polynomial \\(a + b \cdot x + c \cdot x^2\\)
pub struct Poly2(pub Scalar, pub Scalar, pub Scalar);

/// Represents a degree-6 scalar polynomial, without the zeroth degree
/// \\(a \cdot x + b \cdot x^2 + c \cdot x^3 + d \cdot x^4 + e \cdot x^5 + f \cdot x^6\\)
#[cfg(feature = "multiprover")]
pub struct Poly6 {
    pub t1: Scalar,
    pub t2: Scalar,
    pub t3: Scalar,
    pub t4: Scalar,
    pub t5: Scalar,
    pub t6: Scalar,
}

/// Provides an iterator over the powers of a `Scalar`.
///
/// This struct is created by the `exp_iter` function.
pub struct ScalarExp {
    x: Scalar,
    next_exp_x: Scalar,
}

impl Iterator for ScalarExp {
    type Item = Scalar;

    fn next(&mut self) -> Option<Scalar> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter(x: Scalar) -> ScalarExp {
    let next_exp_x = Scalar::from(1);
    ScalarExp { x, next_exp_x }
}

/// Return a result that is the exponentiation chain of the result `x` to the power `n`
pub fn exp_iter_result(x: ScalarResult, n: usize, fabric: &MpcFabric) -> Vec<ScalarResult> {
    let mut res = Vec::with_capacity(n);
    res.push(fabric.one());

    let mut curr_exp = x.clone();
    for _ in 1..n {
        res.push(curr_exp.clone());
        curr_exp = &curr_exp * &x;
    }

    res
}

pub fn add_vec(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    if a.len() != b.len() {
        // throw some error
        //println!("lengths of vectors don't match for vector addition");
    }
    let mut out = vec![Scalar::from(0); b.len()];
    for i in 0..a.len() {
        out[i] = a[i] + b[i];
    }
    out
}

impl VecPoly1 {
    pub fn zero(n: usize) -> Self {
        VecPoly1(vec![Scalar::from(0); n], vec![Scalar::from(0); n])
    }

    pub fn inner_product(&self, rhs: &VecPoly1) -> Poly2 {
        // Uses Karatsuba's method
        let l = self;
        let r = rhs;

        let t0 = inner_product(&l.0, &r.0);
        let t2 = inner_product(&l.1, &r.1);

        let l0_plus_l1 = add_vec(&l.0, &l.1);
        let r0_plus_r1 = add_vec(&r.0, &r.1);

        let t1 = inner_product(&l0_plus_l1, &r0_plus_r1) - t0 - t2;

        Poly2(t0, t1, t2)
    }

    pub fn eval(&self, x: Scalar) -> Vec<Scalar> {
        let n = self.0.len();
        let mut out = vec![Scalar::from(0); n];

        #[allow(clippy::needless_range_loop)]
        for i in 0..n {
            out[i] = self.0[i] + self.1[i] * x;
        }
        out
    }
}

#[cfg(feature = "multiprover")]
impl VecPoly3 {
    pub fn zero(n: usize) -> Self {
        VecPoly3(
            vec![Scalar::from(0); n],
            vec![Scalar::from(0); n],
            vec![Scalar::from(0); n],
            vec![Scalar::from(0); n],
        )
    }

    /// Compute an inner product of `lhs`, `rhs` which have the property that:
    /// - `lhs.0` is zero;
    /// - `rhs.2` is zero;
    /// This is the case in the constraint system proof.
    pub fn special_inner_product(lhs: &Self, rhs: &Self) -> Poly6 {
        // TODO: make checks that l_poly.0 and r_poly.2 are zero.

        let t1 = inner_product(&lhs.1, &rhs.0);
        let t2 = inner_product(&lhs.1, &rhs.1) + inner_product(&lhs.2, &rhs.0);
        let t3 = inner_product(&lhs.2, &rhs.1) + inner_product(&lhs.3, &rhs.0);
        let t4 = inner_product(&lhs.1, &rhs.3) + inner_product(&lhs.3, &rhs.1);
        let t5 = inner_product(&lhs.2, &rhs.3);
        let t6 = inner_product(&lhs.3, &rhs.3);

        Poly6 {
            t1,
            t2,
            t3,
            t4,
            t5,
            t6,
        }
    }

    pub fn eval(&self, x: Scalar) -> Vec<Scalar> {
        let n = self.0.len();
        let mut out = vec![Scalar::from(0); n];

        #[allow(clippy::needless_range_loop)]
        for i in 0..n {
            out[i] = self.0[i] + x * (self.1[i] + x * (self.2[i] + x * self.3[i]));
        }
        out
    }
}

impl Poly2 {
    pub fn eval(&self, x: Scalar) -> Scalar {
        self.0 + x * (self.1 + x * self.2)
    }
}

#[cfg(feature = "multiprover")]
impl Poly6 {
    pub fn eval(&self, x: Scalar) -> Scalar {
        x * (self.t1 + x * (self.t2 + x * (self.t3 + x * (self.t4 + x * (self.t5 + x * self.t6)))))
    }
}

/// Raises `x` to the power `n` using binary exponentiation,
/// with (1 to 2)*lg(n) scalar multiplications.
/// TODO: a constant time version of this would be awfully similar to a Montgomery ladder.
pub fn scalar_exp_vartime(x: &Scalar, mut n: u64) -> Scalar {
    let mut result = Scalar::from(1);
    let mut aux = *x; // x, x^2, x^4, x^8, ...
    while n > 0 {
        let bit = n & 1;
        if bit == 1 {
            result *= aux;
        }
        n >>= 1;
        aux = aux * aux; // FIXME: one unnecessary multiplication at the last step here!
    }
    result
}

/// Takes the sum of all the powers of `x`, up to `n`
/// If `n` is a power of 2, it uses the efficient algorithm with `2*lg n` multiplications and additions.
/// If `n` is not a power of 2, it uses the slow algorithm with `n` multiplications and additions.
/// In the Bulletproofs case, all calls to `sum_of_powers` should have `n` as a power of 2.
pub fn sum_of_powers(x: &Scalar, n: usize) -> Scalar {
    if !n.is_power_of_two() {
        return sum_of_powers_slow(x, n);
    }
    if n == 0 || n == 1 {
        return Scalar::from(n as u64);
    }
    let mut m = n;
    let mut result = Scalar::from(1) + x;
    let mut factor = *x;
    while m > 2 {
        factor = factor * factor;
        result = result + factor * result;
        m /= 2;
    }
    result
}

// takes the sum of all of the powers of x, up to n
fn sum_of_powers_slow(x: &Scalar, n: usize) -> Scalar {
    exp_iter(*x).take(n).sum()
}

/// Given `data` with `len >= 32`, return the first 32 bytes.
pub fn read_exact<const N: usize>(data: &[u8]) -> [u8; N] {
    let mut buf32 = [0u8; N];
    buf32[..].copy_from_slice(&data[..N]);
    buf32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exp_2_is_powers_of_2() {
        let exp_2: Vec<_> = exp_iter(Scalar::from(2u64)).take(4).collect();

        assert_eq!(exp_2[0], Scalar::from(1u64));
        assert_eq!(exp_2[1], Scalar::from(2u64));
        assert_eq!(exp_2[2], Scalar::from(4u64));
        assert_eq!(exp_2[3], Scalar::from(8u64));
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

    #[test]
    fn test_sum_of_powers() {
        let x = Scalar::from(10u64);
        assert_eq!(sum_of_powers_slow(&x, 0), sum_of_powers(&x, 0));
        assert_eq!(sum_of_powers_slow(&x, 1), sum_of_powers(&x, 1));
        assert_eq!(sum_of_powers_slow(&x, 2), sum_of_powers(&x, 2));
        assert_eq!(sum_of_powers_slow(&x, 4), sum_of_powers(&x, 4));
        assert_eq!(sum_of_powers_slow(&x, 8), sum_of_powers(&x, 8));
        assert_eq!(sum_of_powers_slow(&x, 16), sum_of_powers(&x, 16));
        assert_eq!(sum_of_powers_slow(&x, 32), sum_of_powers(&x, 32));
        assert_eq!(sum_of_powers_slow(&x, 64), sum_of_powers(&x, 64));
    }

    #[test]
    fn test_sum_of_powers_slow() {
        let x = Scalar::from(10u64);
        assert_eq!(sum_of_powers_slow(&x, 0), Scalar::from(0));
        assert_eq!(sum_of_powers_slow(&x, 1), Scalar::from(1));
        assert_eq!(sum_of_powers_slow(&x, 2), Scalar::from(11u64));
        assert_eq!(sum_of_powers_slow(&x, 3), Scalar::from(111u64));
        assert_eq!(sum_of_powers_slow(&x, 4), Scalar::from(1111u64));
        assert_eq!(sum_of_powers_slow(&x, 5), Scalar::from(11111u64));
        assert_eq!(sum_of_powers_slow(&x, 6), Scalar::from(111111u64));
    }
}
