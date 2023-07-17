//! Definition of linear combinations.

use core::fmt::{Debug, Formatter, Result};
use core::hash::Hash;
use core::ops::{AddAssign, SubAssign};
use mpc_stark::algebra::scalar::{Scalar, ScalarResult};
use mpc_stark::MpcFabric;
use std::collections::HashMap;
use std::iter::FromIterator;
use std::ops::{Add, Mul, Neg, Sub};

use crate::r1cs::Variable;

/// Represents a variable in a constraint system.
pub struct MpcVariable {
    /// The type of variable this represents in the CS
    var_type: Variable,
    /// The underlying MPC fabric, for allocating
    fabric: MpcFabric,
}

impl Debug for MpcVariable {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.var_type.fmt(f)
    }
}

/// In the hash implementation, ignore the MPC fabric
impl Hash for MpcVariable {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        Hash::hash(&self.var_type, state)
    }
}

impl MpcVariable {
    pub fn get_type(&self) -> Variable {
        self.var_type
    }
}

impl Clone for MpcVariable {
    fn clone(&self) -> Self {
        Self {
            var_type: self.var_type,
            fabric: self.fabric.clone(),
        }
    }
}

impl PartialEq for MpcVariable {
    fn eq(&self, other: &Self) -> bool {
        self.var_type.eq(&other.var_type)
    }
}

impl Eq for MpcVariable {}

impl MpcVariable {
    /// Create a new variable with type
    pub fn new_with_type(var_type: Variable, fabric: MpcFabric) -> Self {
        Self { var_type, fabric }
    }

    /// Create an MpcVariable representing 1
    pub fn one(fabric: MpcFabric) -> Self {
        MpcVariable {
            fabric,
            var_type: Variable::One(),
        }
    }
}

impl From<MpcVariable> for MpcLinearCombination {
    fn from(v: MpcVariable) -> MpcLinearCombination {
        let coeff = v.fabric.one();
        MpcLinearCombination {
            terms: HashMap::from([(v, coeff)]),
        }
    }
}

impl<'a> From<&'a MpcVariable> for MpcLinearCombination {
    fn from(v: &'a MpcVariable) -> Self {
        let coeff = v.fabric.one();
        MpcLinearCombination {
            terms: HashMap::from([(v.clone(), coeff)]),
        }
    }
}

impl From<ScalarResult> for MpcLinearCombination {
    fn from(s: ScalarResult) -> Self {
        let fabric = s.clone_fabric();
        MpcLinearCombination {
            terms: HashMap::from([(MpcVariable::one(fabric), s)]),
        }
    }
}

impl From<&ScalarResult> for MpcLinearCombination {
    fn from(s: &ScalarResult) -> Self {
        let fabric = s.clone_fabric();
        MpcLinearCombination {
            terms: HashMap::from([(MpcVariable::one(fabric), s.clone())]),
        }
    }
}

// Arithmetic on variables produces linear combinations
impl Neg for MpcVariable {
    type Output = MpcLinearCombination;

    fn neg(self) -> Self::Output {
        -MpcLinearCombination::from(self)
    }
}

impl<L: Into<MpcLinearCombination>> Add<L> for MpcVariable {
    type Output = MpcLinearCombination;

    fn add(self, other: L) -> Self::Output {
        MpcLinearCombination::from(self) + other.into()
    }
}

impl<'a, L: Into<MpcLinearCombination>> Add<L> for &'a MpcVariable {
    type Output = MpcLinearCombination;

    fn add(self, other: L) -> Self::Output {
        MpcLinearCombination::from(self) + other.into()
    }
}

impl<L: Into<MpcLinearCombination>> Sub<L> for MpcVariable {
    type Output = MpcLinearCombination;

    fn sub(self, other: L) -> Self::Output {
        MpcLinearCombination::from(self) - other.into()
    }
}

impl<'a, L: Into<MpcLinearCombination>> Sub<L> for &'a MpcVariable {
    type Output = MpcLinearCombination;

    fn sub(self, other: L) -> Self::Output {
        MpcLinearCombination::from(self) - other.into()
    }
}

impl<S: Into<Scalar>> Mul<S> for MpcVariable {
    type Output = MpcLinearCombination;

    fn mul(self, other: S) -> Self::Output {
        let coeff = self.fabric.allocate_scalar(other);
        MpcLinearCombination {
            terms: HashMap::from([(self, coeff)]),
        }
    }
}

// Arithmetic on scalars with variables produces linear combinations
impl<'a> Add<&'a MpcVariable> for Scalar {
    type Output = MpcLinearCombination;

    fn add(self, other: &'a MpcVariable) -> Self::Output {
        self + other.clone()
    }
}

impl Add<MpcVariable> for Scalar {
    type Output = MpcLinearCombination;

    fn add(self, other: MpcVariable) -> Self::Output {
        let self_lc: MpcLinearCombination =
            MpcLinearCombination::from_scalar(self, other.fabric.clone());
        let other_lc: MpcLinearCombination = other.into();
        self_lc + other_lc
    }
}

impl<'a> Sub<&'a MpcVariable> for Scalar {
    type Output = MpcLinearCombination;

    fn sub(self, other: &'a MpcVariable) -> Self::Output {
        self - other.clone()
    }
}

impl<'a> Sub<Scalar> for &'a MpcVariable {
    type Output = MpcLinearCombination;

    fn sub(self, other: Scalar) -> Self::Output {
        self.clone() - other
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl Sub<Scalar> for MpcVariable {
    type Output = MpcLinearCombination;

    fn sub(self, other: Scalar) -> Self::Output {
        other.neg() + self
    }
}

impl Sub<MpcVariable> for Scalar {
    type Output = MpcLinearCombination;

    fn sub(self, other: MpcVariable) -> Self::Output {
        other - self
    }
}

impl<'a> Mul<&'a MpcVariable> for Scalar {
    type Output = MpcLinearCombination;

    fn mul(self, other: &'a MpcVariable) -> Self::Output {
        self * other.clone()
    }
}

impl Mul<MpcVariable> for Scalar {
    type Output = MpcLinearCombination;

    fn mul(self, other: MpcVariable) -> Self::Output {
        let coeff = other.fabric.allocate_scalar(self);
        MpcLinearCombination {
            terms: HashMap::from([(other, coeff)]),
        }
    }
}

/// Represents a linear combination of
/// [`MpcVariables`](::r1cs::MpcVariable).  Each term is represented by a
/// `(MpcVariable, Scalar)` pair.
#[derive(Debug, Default)]
pub struct MpcLinearCombination {
    pub(crate) terms: HashMap<MpcVariable, ScalarResult>,
}

impl MpcLinearCombination {
    /// Instead of exposing the underlying HashMap interface, this method allows a
    /// caller to add a single term to the linear combination
    pub fn add_term(&mut self, var: MpcVariable, coeff: ScalarResult) {
        if let Some(existing_coeff) = self.terms.get(&var) {
            self.terms.insert(var, existing_coeff + coeff);
        } else {
            self.terms.insert(var, coeff);
        }
    }
}

impl Clone for MpcLinearCombination {
    fn clone(&self) -> Self {
        MpcLinearCombination {
            terms: self.terms.clone(),
        }
    }
}

impl MpcLinearCombination {
    pub fn from_scalar(scalar: Scalar, fabric: MpcFabric) -> Self {
        Self {
            terms: HashMap::from([(
                MpcVariable::one(fabric.clone()),
                fabric.allocate_scalar(scalar),
            )]),
        }
    }
}

impl FromIterator<(MpcVariable, Scalar)> for MpcLinearCombination {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (MpcVariable, Scalar)>,
    {
        MpcLinearCombination {
            terms: iter
                .into_iter()
                .map(|(var, coeff)| {
                    let coeff = var.fabric.allocate_scalar(coeff);
                    (var, coeff)
                })
                .collect(),
        }
    }
}

// Arithmetic on linear combinations

impl<L: Into<MpcLinearCombination>> Add<L> for MpcLinearCombination {
    type Output = Self;

    fn add(mut self, rhs: L) -> Self::Output {
        self += rhs.into();
        self
    }
}

impl<'a, L: Into<MpcLinearCombination>> Add<L> for &'a MpcLinearCombination {
    type Output = MpcLinearCombination;

    fn add(self, rhs: L) -> Self::Output {
        let mut self_clone = self.clone();
        self_clone += rhs.into();
        self_clone
    }
}

impl<L: Into<MpcLinearCombination>> AddAssign<L> for MpcLinearCombination {
    fn add_assign(&mut self, rhs: L) {
        for (var, coeff) in rhs.into().terms.iter() {
            if let Some(lhs_value) = self.terms.get(var) {
                self.terms.insert(var.clone(), lhs_value + coeff);
            } else {
                self.terms.insert(var.clone(), coeff.clone());
            }
        }
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<L: Into<MpcLinearCombination>> Sub<L> for MpcLinearCombination {
    type Output = Self;

    fn sub(self, rhs: L) -> Self::Output {
        let mut self_clone = self;
        self_clone += rhs.into().neg();
        self_clone
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<'a, L: Into<MpcLinearCombination>> Sub<L> for &'a MpcLinearCombination {
    type Output = MpcLinearCombination;

    fn sub(self, rhs: L) -> Self::Output {
        let mut self_clone = self.clone();
        self_clone += rhs.into().neg();
        self_clone
    }
}

#[allow(clippy::suspicious_op_assign_impl)]
impl<L: Into<MpcLinearCombination>> SubAssign<L> for MpcLinearCombination {
    fn sub_assign(&mut self, rhs: L) {
        *self += rhs.into().neg();
    }
}

impl Mul<MpcLinearCombination> for Scalar {
    type Output = MpcLinearCombination;

    fn mul(self, other: MpcLinearCombination) -> Self::Output {
        let out_terms = other
            .terms
            .into_iter()
            .map(|(var, scalar)| (var, scalar * self))
            .collect();
        MpcLinearCombination { terms: out_terms }
    }
}

impl<'a> Mul<&'a MpcLinearCombination> for Scalar {
    type Output = MpcLinearCombination;

    fn mul(self, rhs: &'a MpcLinearCombination) -> Self::Output {
        self * rhs.clone()
    }
}

impl Neg for MpcLinearCombination {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        self.terms = self
            .terms
            .into_iter()
            .map(|(var, coeff)| (var, coeff.neg()))
            .collect();
        self
    }
}

impl<'a> Neg for &'a MpcLinearCombination {
    type Output = MpcLinearCombination;

    fn neg(self) -> Self::Output {
        self.clone().neg()
    }
}

impl<S: Into<Scalar>> Mul<S> for MpcLinearCombination {
    type Output = Self;

    fn mul(mut self, other: S) -> Self::Output {
        let other = other.into();
        for (_, s) in self.terms.iter_mut() {
            *s = &*s * other
        }
        self
    }
}
