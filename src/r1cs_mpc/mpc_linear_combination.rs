//! Definition of linear combinations.

use core::cell::Ref;
use curve25519_dalek::scalar::Scalar;
use mpc_ristretto::authenticated_scalar::AuthenticatedScalar;
use mpc_ristretto::beaver::SharedValueSource;
use mpc_ristretto::fabric::AuthenticatedMpcFabric;
use mpc_ristretto::network::MpcNetwork;
use std::iter::FromIterator;
use std::ops::{Add, Mul, Neg, Sub};

use crate::r1cs::Variable;

use super::mpc_prover::SharedMpcFabric;

/// Represents a variable in a constraint system.
#[derive(Debug)]
pub struct MpcVariable<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> {
    /// The type of variable this repsents in the CS
    var_type: Variable,
    /// The underlying MPC fabric, for allocating
    fabric: SharedMpcFabric<N, S>,
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> MpcVariable<N, S> {
    pub fn get_type(&self) -> Variable {
        self.var_type
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Clone for MpcVariable<N, S> {
    fn clone(&self) -> Self {
        Self {
            var_type: self.var_type,
            fabric: self.fabric.clone(),
        }
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> PartialEq for MpcVariable<N, S> {
    fn eq(&self, other: &Self) -> bool {
        self.var_type.eq(&other.var_type)
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Eq for MpcVariable<N, S> {}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> MpcVariable<N, S> {
    /// Create a new variable with type
    pub fn new_with_type(var_type: Variable, fabric: SharedMpcFabric<N, S>) -> Self {
        Self { var_type, fabric }
    }

    /// Borrow a reference to the underlying MPC fabric
    fn borrow_fabric(&self) -> Ref<AuthenticatedMpcFabric<N, S>> {
        self.fabric.as_ref().borrow()
    }

    /// Create an MpcVariable representing 1
    fn one(fabric: SharedMpcFabric<N, S>) -> Self {
        MpcVariable {
            fabric,
            var_type: Variable::One(),
        }
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> From<MpcVariable<N, S>>
    for MpcLinearCombination<N, S>
{
    fn from(v: MpcVariable<N, S>) -> MpcLinearCombination<N, S> {
        let coeff = v.borrow_fabric().allocate_public_scalar(Scalar::zero());
        MpcLinearCombination {
            terms: vec![(v, coeff)],
        }
    }
}

// Arithmetic on variables produces linear combinations
impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Neg for MpcVariable<N, S> {
    type Output = MpcLinearCombination<N, S>;

    fn neg(self) -> Self::Output {
        -MpcLinearCombination::from(self)
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>, L: Into<MpcLinearCombination<N, S>>> Add<L>
    for MpcVariable<N, S>
{
    type Output = MpcLinearCombination<N, S>;

    fn add(self, other: L) -> Self::Output {
        MpcLinearCombination::from(self) + other.into()
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>, L: Into<MpcLinearCombination<N, S>>> Sub<L>
    for MpcVariable<N, S>
{
    type Output = MpcLinearCombination<N, S>;

    fn sub(self, other: L) -> Self::Output {
        MpcLinearCombination::from(self) - other.into()
    }
}

impl<N: MpcNetwork + Send, Sh: SharedValueSource<Scalar>, S: Into<Scalar>> Mul<S>
    for MpcVariable<N, Sh>
{
    type Output = MpcLinearCombination<N, Sh>;

    fn mul(self, other: S) -> Self::Output {
        let coeff = self.borrow_fabric().allocate_public_scalar(other.into());
        MpcLinearCombination {
            terms: vec![(self, coeff)],
        }
    }
}

// Arithmetic on scalars with variables produces linear combinations
impl<'a, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Add<&'a MpcVariable<N, S>> for Scalar {
    type Output = MpcLinearCombination<N, S>;

    fn add(self, other: &'a MpcVariable<N, S>) -> Self::Output {
        self + other.clone()
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Add<MpcVariable<N, S>> for Scalar {
    type Output = MpcLinearCombination<N, S>;

    fn add(self, other: MpcVariable<N, S>) -> Self::Output {
        let self_scalar = other.borrow_fabric().allocate_public_scalar(self);
        let one = other.borrow_fabric().allocate_public_scalar(Scalar::one());
        MpcLinearCombination {
            terms: vec![
                (MpcVariable::one(other.fabric.clone()), self_scalar),
                (other, one),
            ],
        }
    }
}

impl<'a, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Add<&'a MpcVariable<N, S>>
    for AuthenticatedScalar<N, S>
{
    type Output = MpcLinearCombination<N, S>;

    fn add(self, other: &'a MpcVariable<N, S>) -> Self::Output {
        self + other.clone()
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Add<MpcVariable<N, S>>
    for AuthenticatedScalar<N, S>
{
    type Output = MpcLinearCombination<N, S>;

    fn add(self, other: MpcVariable<N, S>) -> Self::Output {
        let one = other.borrow_fabric().allocate_public_scalar(Scalar::one());
        MpcLinearCombination {
            terms: vec![(MpcVariable::one(other.fabric.clone()), self), (other, one)],
        }
    }
}

impl<'a, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Sub<&'a MpcVariable<N, S>> for Scalar {
    type Output = MpcLinearCombination<N, S>;

    fn sub(self, other: &'a MpcVariable<N, S>) -> Self::Output {
        self - other.clone()
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Sub<MpcVariable<N, S>> for Scalar {
    type Output = MpcLinearCombination<N, S>;

    fn sub(self, other: MpcVariable<N, S>) -> Self::Output {
        let self_scalar = other.borrow_fabric().allocate_public_scalar(self);
        let negative_one = other.borrow_fabric().allocate_public_scalar(-Scalar::one());
        MpcLinearCombination {
            terms: vec![
                (MpcVariable::one(other.fabric.clone()), self_scalar),
                (other, negative_one),
            ],
        }
    }
}

impl<'a, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Sub<&'a MpcVariable<N, S>>
    for AuthenticatedScalar<N, S>
{
    type Output = MpcLinearCombination<N, S>;

    fn sub(self, other: &'a MpcVariable<N, S>) -> Self::Output {
        self - other.clone()
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Sub<MpcVariable<N, S>>
    for AuthenticatedScalar<N, S>
{
    type Output = MpcLinearCombination<N, S>;

    fn sub(self, other: MpcVariable<N, S>) -> Self::Output {
        let negative_one = other.borrow_fabric().allocate_public_scalar(-Scalar::one());
        MpcLinearCombination {
            terms: vec![
                (MpcVariable::one(other.fabric.clone()), self),
                (other, negative_one),
            ],
        }
    }
}

impl<'a, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Mul<&'a MpcVariable<N, S>> for Scalar {
    type Output = MpcLinearCombination<N, S>;

    fn mul(self, other: &'a MpcVariable<N, S>) -> Self::Output {
        self * other.clone()
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Mul<MpcVariable<N, S>> for Scalar {
    type Output = MpcLinearCombination<N, S>;

    fn mul(self, other: MpcVariable<N, S>) -> Self::Output {
        let coeff = other.borrow_fabric().allocate_public_scalar(self);
        MpcLinearCombination {
            terms: vec![(other, coeff)],
        }
    }
}

impl<'a, N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Mul<&'a MpcVariable<N, S>>
    for AuthenticatedScalar<N, S>
{
    type Output = MpcLinearCombination<N, S>;

    fn mul(self, other: &'a MpcVariable<N, S>) -> Self::Output {
        self * other.clone()
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Mul<MpcVariable<N, S>>
    for AuthenticatedScalar<N, S>
{
    type Output = MpcLinearCombination<N, S>;

    fn mul(self, other: MpcVariable<N, S>) -> Self::Output {
        MpcLinearCombination {
            terms: vec![(other, self)],
        }
    }
}

/// Represents a linear combination of
/// [`MpcVariables`](::r1cs::MpcVariable).  Each term is represented by a
/// `(MpcVariable, Scalar)` pair.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MpcLinearCombination<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> {
    pub(crate) terms: Vec<(MpcVariable<N, S>, AuthenticatedScalar<N, S>)>,
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> MpcLinearCombination<N, S> {
    pub fn from_scalar(scalar: Scalar, fabric: SharedMpcFabric<N, S>) -> Self {
        Self {
            terms: vec![(
                MpcVariable::one(fabric.clone()),
                fabric.as_ref().borrow().allocate_public_scalar(scalar),
            )],
        }
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> FromIterator<(MpcVariable<N, S>, Scalar)>
    for MpcLinearCombination<N, S>
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (MpcVariable<N, S>, Scalar)>,
    {
        MpcLinearCombination {
            terms: iter
                .into_iter()
                .map(|(var, coeff)| {
                    let coeff = var.borrow_fabric().allocate_public_scalar(coeff);
                    (var, coeff)
                })
                .collect(),
        }
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>>
    FromIterator<(MpcVariable<N, S>, AuthenticatedScalar<N, S>)> for MpcLinearCombination<N, S>
{
    fn from_iter<T: IntoIterator<Item = (MpcVariable<N, S>, AuthenticatedScalar<N, S>)>>(
        iter: T,
    ) -> Self {
        MpcLinearCombination {
            terms: iter.into_iter().collect(),
        }
    }
}

impl<'a, N: MpcNetwork + Send, S: SharedValueSource<Scalar>>
    FromIterator<&'a (MpcVariable<N, S>, Scalar)> for MpcLinearCombination<N, S>
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = &'a (MpcVariable<N, S>, Scalar)>,
    {
        MpcLinearCombination {
            terms: iter
                .into_iter()
                .map(|(var, coeff)| {
                    (
                        var.clone(),
                        var.borrow_fabric().allocate_public_scalar(*coeff),
                    )
                })
                .collect::<Vec<(_, _)>>(),
        }
    }
}

impl<'a, N: 'a + MpcNetwork + Send, S: 'a + SharedValueSource<Scalar>>
    FromIterator<&'a (MpcVariable<N, S>, AuthenticatedScalar<N, S>)>
    for MpcLinearCombination<N, S>
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = &'a (MpcVariable<N, S>, AuthenticatedScalar<N, S>)>,
    {
        MpcLinearCombination {
            terms: iter.into_iter().cloned().collect(),
        }
    }
}

// Arithmetic on linear combinations

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>, L: Into<MpcLinearCombination<N, S>>> Add<L>
    for MpcLinearCombination<N, S>
{
    type Output = Self;

    fn add(mut self, rhs: L) -> Self::Output {
        self.terms.extend(
            rhs.into()
                .terms
                .iter()
                .map(|(var, coeff)| (var.clone(), coeff.clone())),
        );
        MpcLinearCombination { terms: self.terms }
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>, L: Into<MpcLinearCombination<N, S>>> Sub<L>
    for MpcLinearCombination<N, S>
{
    type Output = Self;

    fn sub(mut self, rhs: L) -> Self::Output {
        self.terms.extend(
            rhs.into()
                .terms
                .iter()
                .map(|(var, coeff)| (var.clone(), -coeff)),
        );
        MpcLinearCombination { terms: self.terms }
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Mul<MpcLinearCombination<N, S>>
    for Scalar
{
    type Output = MpcLinearCombination<N, S>;

    fn mul(self, other: MpcLinearCombination<N, S>) -> Self::Output {
        let out_terms = other
            .terms
            .into_iter()
            .map(|(var, scalar)| (var, scalar * self))
            .collect();
        MpcLinearCombination { terms: out_terms }
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Mul<MpcLinearCombination<N, S>>
    for AuthenticatedScalar<N, S>
{
    type Output = MpcLinearCombination<N, S>;

    fn mul(self, other: MpcLinearCombination<N, S>) -> Self::Output {
        let out_terms = other
            .terms
            .into_iter()
            .map(|(var, coeff)| (var, coeff * &self))
            .collect();
        MpcLinearCombination { terms: out_terms }
    }
}

impl<N: MpcNetwork + Send, S: SharedValueSource<Scalar>> Neg for MpcLinearCombination<N, S> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for (_, s) in self.terms.iter_mut() {
            *s = -s.clone()
        }
        self
    }
}

impl<N: MpcNetwork + Send, Sh: SharedValueSource<Scalar>, S: Into<Scalar>> Mul<S>
    for MpcLinearCombination<N, Sh>
{
    type Output = Self;

    fn mul(mut self, other: S) -> Self::Output {
        let other = other.into();
        for (_, s) in self.terms.iter_mut() {
            *s *= other
        }
        self
    }
}
