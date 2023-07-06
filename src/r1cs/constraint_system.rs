//! Definition of the constraint system trait.

use std::collections::HashSet;

use super::{LinearCombination, R1CSError, Variable};
use merlin::Transcript;
use mpc_stark::algebra::scalar::Scalar;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, Default)]
pub struct SparseWeightRow(pub Vec<(usize, Scalar)>);

impl PartialEq for SparseWeightRow {
    fn eq(&self, other: &Self) -> bool {
        // Because sparse constraint representation is constructed by iterating over (K, V) pairs
        // of underlying linear combinations, order of terms in the matrix is not guaranteed.
        // This is okay, because the matrix elements contain the index of the variable
        // to which the given weight is applied, but requires us to have an
        // ordering-agnostic equality relation
        let a: HashSet<&(usize, Scalar)> = self.0.iter().collect();
        let b: HashSet<&(usize, Scalar)> = other.0.iter().collect();

        a == b
    }
}
impl Eq for SparseWeightRow {}

// When extracting the weights from a [`LinearCombination`], it may or may not
// have a constant term, which is represented by an `Option<Scalar>`.
// When we try to unzip the weights collected from multiple [`LinearCombination`]s into a
// [`CircuitWeights`] struct, we need to be able to extend a [`SparseWeightRow`] with a
// `(usize, Option<Scalar>)` in order to build the `c` vector.
impl Extend<(usize, Option<Scalar>)> for SparseWeightRow {
    fn extend<T: IntoIterator<Item = (usize, Option<Scalar>)>>(&mut self, iter: T) {
        self.0.extend(
            iter.into_iter()
                .filter_map(|(i, maybe_c_i)| maybe_c_i.map(|c_i| (i, c_i))),
        )
    }
}

#[derive(Debug, Serialize, Deserialize, Default, PartialEq, Eq)]
pub struct SparseReducedMatrix(pub Vec<SparseWeightRow>);

impl Extend<SparseWeightRow> for SparseReducedMatrix {
    fn extend<T: IntoIterator<Item = SparseWeightRow>>(&mut self, iter: T) {
        self.0.extend(iter)
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct CircuitWeights {
    pub w_l: SparseReducedMatrix,
    pub w_r: SparseReducedMatrix,
    pub w_o: SparseReducedMatrix,
    pub w_v: SparseReducedMatrix,
    pub c: SparseWeightRow,
}

/// The interface for a constraint system, abstracting over the prover
/// and verifier's roles.
///
/// Statements to be proved by an [`R1CSProof`](::r1cs::R1CSProof) are specified by
/// programmatically constructing constraints.  These constraints need
/// to be identical between the prover and verifier, since the prover
/// and verifier need to construct the same statement.
///
/// To prevent code duplication or mismatches between the prover and
/// verifier, gadgets for the constraint system should be written
/// using the `ConstraintSystem` trait, so that the prover and
/// verifier share the logic for specifying constraints.
pub trait ConstraintSystem {
    /// Leases the proof transcript to the user, so they can
    /// add extra data to which the proof must be bound, but which
    /// is not available before creation of the constraint system.
    fn transcript(&mut self) -> &mut Transcript;

    /// Allocate and constrain multiplication variables.
    ///
    /// Allocate variables `left`, `right`, and `out`
    /// with the implicit constraint that
    /// ```text
    /// left * right = out
    /// ```
    /// and add the explicit constraints that
    /// ```text
    /// left = left_constraint
    /// right = right_constraint
    /// ```
    ///
    /// Returns `(left, right, out)` for use in further constraints.
    fn multiply(
        &mut self,
        left: LinearCombination,
        right: LinearCombination,
    ) -> (Variable, Variable, Variable);

    /// Fetch the number of constraints currently registered in the prover
    ///
    /// Used as a profiling metric
    fn num_constraints(&self) -> usize;

    /// Fetch the number of multiplication gates registered in the prover
    ///
    /// Used as a profiling metric
    fn num_multipliers(&self) -> usize;

    /// Get the sparse-reduced weight matrices & constant vector representing
    /// the constraint system
    ///
    /// Used so that the publicly-known "structure" of the constraint system
    /// can be exported
    fn get_weights(&self) -> CircuitWeights;

    /// Allocate a single variable.
    ///
    /// This either allocates a new multiplier and returns its `left` variable,
    /// or returns a `right` variable of a multiplier previously allocated by this method.
    /// The output of a multiplier is assigned on a even call, when `right` is assigned.
    ///
    /// When CS is committed at the end of the first or second phase, the half-assigned multiplier
    /// has the `right` assigned to zero and all its variables committed.
    ///
    /// Returns unconstrained `Variable` for use in further constraints.
    fn allocate(&mut self, assignment: Option<Scalar>) -> Result<Variable, R1CSError>;

    /// Allocate variables `left`, `right`, and `out`
    /// with the implicit constraint that
    /// ```text
    /// left * right = out
    /// ```
    ///
    /// Returns `(left, right, out)` for use in further constraints.
    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError>;

    /// Creates a commitment to a public input (also referred to as a "statement variable")
    ///
    /// This commitment interface allows the verifier to input the
    /// value to be committed, as opposed to simply recording the value committed to by
    /// the prover. We provide this interface to allow the verifier to specify the public
    /// variables to the proof, a necessary step to ensure the validity of the *correct*
    /// statement.
    ///
    /// # Inputs
    ///
    /// The value to be committed by the verifier, as a Scalar. This value should (as above)
    /// be passed upfront, so that its commitment can be recorded in the Fiat-Shamir
    /// transcript.
    ///
    /// # Returns
    ///
    /// Returns a `Variable` that can be used to refer to this commited value in constraint
    /// generation.
    fn commit_public(&mut self, value: Scalar) -> Variable;

    /// Enforce the explicit constraint that
    /// ```text
    /// lc = 0
    /// ```
    fn constrain(&mut self, lc: LinearCombination);

    /// Evaluate a linear combination using the values allocated in the constraint system
    fn eval(&self, lc: &LinearCombination) -> Scalar;
}

/// An extension to the constraint system trait that permits randomized constraints.
/// Gadgets that do not use randomization should use trait bound `CS: ConstraintSystem`,
/// while gadgets that need randomization should use trait bound `CS: RandomizedConstraintSystem`.
/// Gadgets generally _should not_ use this trait as a bound on the CS argument: it should be used
/// by the higher-order protocol that composes gadgets together.
pub trait RandomizableConstraintSystem: ConstraintSystem {
    /// Represents a concrete type for the CS in a randomization phase.
    type RandomizedCS: RandomizedConstraintSystem;

    /// Specify additional variables and constraints randomized using a challenge scalar
    /// bound to the assignments of the non-randomized variables.
    ///
    /// If the constraint system’s low-level variables have not been committed yet,
    /// the call returns `Ok()` and saves a callback until later.
    ///
    /// If the constraint system’s low-level variables are committed already,
    /// the callback is invoked immediately and its result is return from this method.
    ///
    /// ### Usage
    ///
    /// Inside the closure you can generate one or more challenges using `challenge_scalar` method.
    ///
    /// ```text
    /// cs.specify_randomized_constraints(move |cs| {
    ///     let z = cs.challenge_scalar(b"some challenge");
    ///     // ...
    /// })
    /// ```
    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        F: 'static + Fn(&mut Self::RandomizedCS) -> Result<(), R1CSError>;
}

/// Represents a constraint system in the second phase:
/// when the challenges can be sampled to create randomized constraints.
///
/// Note: this trait also includes `ConstraintSystem` trait
/// in order to allow composition of gadgets: e.g. a shuffle gadget can be used in both phases.
pub trait RandomizedConstraintSystem: ConstraintSystem {
    /// Generates a challenge scalar.
    ///
    /// ### Usage
    ///
    /// This method is available only within the scope of a closure provided
    /// to `specify_randomized_constraints`, which implements
    /// the "randomization" phase of the protocol.
    ///
    /// Arbitrary number of challenges can be generated with additional calls.
    ///
    /// ```text
    /// cs.specify_randomized_constraints(move |cs| {
    ///     let z = cs.challenge_scalar(b"some challenge");
    ///     // ...
    /// })
    /// ```
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar;
}
