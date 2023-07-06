//! Definition of linear combinations.

use core::ops::{AddAssign, MulAssign, SubAssign};
use std::collections::HashMap;
use std::iter::FromIterator;
use std::ops::{Add, Mul, Neg, Sub};

use mpc_stark::algebra::scalar::Scalar;

use super::constraint_system::SparseWeightRow;

/// Represents a variable in a constraint system.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Variable {
    /// Represents an external input specified by a commitment.
    Committed(usize),
    /// Represents the left input of a multiplication gate.
    MultiplierLeft(usize),
    /// Represents the right input of a multiplication gate.
    MultiplierRight(usize),
    /// Represents the output of a multiplication gate.
    MultiplierOutput(usize),
    /// Represents the constant 1.
    One(),
    /// Represents the constant 0.
    Zero(),
}

impl From<Variable> for LinearCombination {
    fn from(v: Variable) -> LinearCombination {
        LinearCombination {
            terms: HashMap::from([(v, Scalar::one())]),
        }
    }
}

impl<S: Into<Scalar>> From<S> for LinearCombination {
    fn from(s: S) -> LinearCombination {
        LinearCombination {
            terms: HashMap::from([(Variable::One(), s.into())]),
        }
    }
}

// Arithmetic on variables produces linear combinations

impl Neg for Variable {
    type Output = LinearCombination;

    fn neg(self) -> Self::Output {
        -LinearCombination::from(self)
    }
}

impl<L: Into<LinearCombination>> Add<L> for Variable {
    type Output = LinearCombination;

    fn add(self, other: L) -> Self::Output {
        LinearCombination::from(self) + other.into()
    }
}

impl<L: Into<LinearCombination>> Sub<L> for Variable {
    type Output = LinearCombination;

    fn sub(self, other: L) -> Self::Output {
        LinearCombination::from(self) - other.into()
    }
}

impl<S: Into<Scalar>> Mul<S> for Variable {
    type Output = LinearCombination;

    fn mul(self, other: S) -> Self::Output {
        LinearCombination {
            terms: HashMap::from([(self, other.into())]),
        }
    }
}

// Arithmetic on scalars with variables produces linear combinations

impl Add<Variable> for Scalar {
    type Output = LinearCombination;

    fn add(self, other: Variable) -> Self::Output {
        // Cast both into linear combinations and merge them
        let self_lc: LinearCombination = self.into();
        let other_lc: LinearCombination = other.into();
        self_lc + other_lc
    }
}

impl Sub<Variable> for Scalar {
    type Output = LinearCombination;

    fn sub(self, other: Variable) -> Self::Output {
        let self_lc: LinearCombination = self.into();
        let other_lc: LinearCombination = other.into();
        self_lc - other_lc
    }
}

impl Mul<Variable> for Scalar {
    type Output = LinearCombination;

    fn mul(self, other: Variable) -> Self::Output {
        LinearCombination {
            terms: HashMap::from([(other, self)]),
        }
    }
}

/// Represents a linear combination of
/// [`Variables`](::r1cs::Variable).  Each term is represented by a
/// `(Variable, Scalar)` pair.
#[derive(Clone, Debug, Default)]
pub struct LinearCombination {
    pub(crate) terms: HashMap<Variable, Scalar>,
}

impl LinearCombination {
    /// Adds a full term, variable and coefficient
    ///
    /// We do not wish to expose the underlying hashmap abstraction,
    /// so this method allows for what would be an `insert`, but with
    /// the optimization that it adds keys which already exist
    pub fn add_term(&mut self, var: Variable, coeff: Scalar) {
        if let Some(existing_coeff) = self.terms.get(&var) {
            self.terms.insert(var, coeff + existing_coeff);
        } else {
            self.terms.insert(var, coeff);
        }
    }

    /// Extracts the non-zero weights for the left, right, output,
    /// and witness variables, and for the constant terms, into
    /// rows of the sparse-reduced weight matrices
    pub fn extract_weights(
        &self,
    ) -> (
        SparseWeightRow,
        SparseWeightRow,
        SparseWeightRow,
        SparseWeightRow,
        Option<Scalar>,
    ) {
        // Each LC can have up to `n` non-zero terms of each variable
        // and a single constant

        let mut w_l_row = SparseWeightRow(Vec::new());
        let mut w_r_row = SparseWeightRow(Vec::new());
        let mut w_o_row = SparseWeightRow(Vec::new());
        let mut w_v_row = SparseWeightRow(Vec::new());
        let mut c = None;

        self.terms
            .iter()
            .filter(|(_, &coeff)| coeff != Scalar::zero())
            .for_each(|(&var, &coeff)| match var {
                Variable::MultiplierLeft(i) => {
                    w_l_row.0.push((i, coeff));
                }
                Variable::MultiplierRight(i) => {
                    w_r_row.0.push((i, coeff));
                }
                Variable::MultiplierOutput(i) => {
                    w_o_row.0.push((i, coeff));
                }
                Variable::Committed(i) => {
                    w_v_row.0.push((i, -coeff));
                }
                Variable::One() => {
                    c = Some(-coeff);
                }
                Variable::Zero() => {}
            });

        (w_l_row, w_r_row, w_o_row, w_v_row, c)
    }
}

impl FromIterator<(Variable, Scalar)> for LinearCombination {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Variable, Scalar)>,
    {
        LinearCombination {
            terms: iter.into_iter().collect(),
        }
    }
}

impl<'a> FromIterator<&'a (Variable, Scalar)> for LinearCombination {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = &'a (Variable, Scalar)>,
    {
        LinearCombination {
            terms: iter.into_iter().cloned().collect(),
        }
    }
}

// Arithmetic on linear combinations

impl<L: Into<LinearCombination>> Add<L> for LinearCombination {
    type Output = Self;

    fn add(mut self, rhs: L) -> Self::Output {
        self += rhs.into();
        self
    }
}

impl<L: Into<LinearCombination>> AddAssign<L> for LinearCombination {
    fn add_assign(&mut self, rhs: L) {
        // For each term in the RHS, add it to the LHS linear combination.
        // If a term involving the RHS variable already exists in the LHS,
        // simply add their coefficients
        for (var, coeff) in rhs.into().terms.iter() {
            if let Some(lhs_value) = self.terms.get(var) {
                self.terms.insert(*var, *lhs_value + *coeff);
            } else {
                self.terms.insert(*var, *coeff);
            }
        }
    }
}

impl<L: Into<LinearCombination>> Sub<L> for LinearCombination {
    type Output = Self;

    fn sub(mut self, rhs: L) -> Self::Output {
        self -= rhs;
        LinearCombination { terms: self.terms }
    }
}

impl<L: Into<LinearCombination>> SubAssign<L> for LinearCombination {
    fn sub_assign(&mut self, rhs: L) {
        let rhs_lc: LinearCombination = rhs.into();
        for (var, coeff) in rhs_lc.terms.iter() {
            if let Some(existing_coeff) = self.terms.get(var) {
                self.terms.insert(*var, existing_coeff - coeff);
            } else {
                self.terms.insert(*var, -coeff);
            }
        }
    }
}

impl Mul<LinearCombination> for Scalar {
    type Output = LinearCombination;

    fn mul(self, other: LinearCombination) -> Self::Output {
        let out_terms = other
            .terms
            .into_iter()
            .map(|(var, scalar)| (var, scalar * self))
            .collect();
        LinearCombination { terms: out_terms }
    }
}

impl MulAssign<Scalar> for LinearCombination {
    fn mul_assign(&mut self, rhs: Scalar) {
        for (_, coeff) in self.terms.iter_mut() {
            *coeff = *coeff * rhs
        }
    }
}

impl Neg for LinearCombination {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for (_, s) in self.terms.iter_mut() {
            *s = s.neg()
        }
        self
    }
}

impl<S: Into<Scalar>> Mul<S> for LinearCombination {
    type Output = Self;

    fn mul(mut self, other: S) -> Self::Output {
        let other = other.into();
        for (_, s) in self.terms.iter_mut() {
            *s *= other
        }
        self
    }
}

#[cfg(test)]
mod tests {
    use merlin::Transcript;
    use mpc_stark::algebra::scalar::Scalar;

    use crate::{
        r1cs::{ConstraintSystem, Prover},
        PedersenGens,
    };

    use super::Variable;

    /// Tests a simple case that was previously buggy; subtracting one from one should give zero
    #[test]
    fn test_subtraction() {
        let one_var = Variable::One();
        let res = one_var - Scalar::one();

        // Evaluate this in a constraint system for posterity sake
        let mut prover_transcript = Transcript::new("test".as_bytes());
        let pc_gens = PedersenGens::default();
        let cs = Prover::new(&pc_gens, &mut prover_transcript);

        let eval_res = cs.eval(&res);
        assert_eq!(eval_res, Scalar::zero());
    }
}
