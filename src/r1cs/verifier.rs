#![allow(non_snake_case)]

use itertools::Itertools;
use merlin::HashChainTranscript as Transcript;
use mpc_stark::algebra::scalar::Scalar;
use mpc_stark::algebra::stark_curve::StarkPoint;

use super::{
    CircuitWeights, ConstraintSystem, LinearCombination, R1CSProof, RandomizableConstraintSystem,
    RandomizedConstraintSystem, Variable,
};

use crate::errors::R1CSError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::transcript::TranscriptProtocol;

/// A [`ConstraintSystem`] implementation for use by the verifier.
///
/// The verifier adds high-level variable commitments to the transcript,
/// allocates low-level variables and creates constraints in terms of these
/// high-level variables and low-level variables.
///
/// When all constraints are added, the verifying code calls `verify`
/// which consumes the `Verifier` instance, samples random challenges
/// that instantiate the randomized constraints, and verifies the proof.
pub struct Verifier<'t, 'g> {
    transcript: &'t mut Transcript,
    pc_gens: &'g PedersenGens,
    constraints: Vec<LinearCombination>,

    /// Records the number of low-level variables allocated in the
    /// constraint system.
    ///
    /// Because the `VerifierCS` only keeps the constraints
    /// themselves, it doesn't record the assignments (they're all
    /// `Missing`), so the `num_vars` isn't kept implicitly in the
    /// variable assignments.
    num_vars: usize,
    V: Vec<StarkPoint>,

    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    /// After that, the option will flip to None and additional calls to `randomize_constraints`
    /// will invoke closures immediately.
    #[allow(clippy::type_complexity)]
    deferred_constraints:
        Vec<Box<dyn Fn(&mut RandomizingVerifier<'t, 'g>) -> Result<(), R1CSError>>>,

    /// Index of a pending multiplier that's not fully assigned yet.
    pending_multiplier: Option<usize>,
}

/// Verifier in the randomizing phase.
///
/// Note: this type is exported because it is used to specify the associated type
/// in the public impl of a trait `ConstraintSystem`, which boils down to allowing compiler to
/// monomorphize the closures for the proving and verifying code.
/// However, this type cannot be instantiated by the user and therefore can only be used within
/// the callback provided to `specify_randomized_constraints`.
pub struct RandomizingVerifier<'t, 'g> {
    verifier: Verifier<'t, 'g>,
}

impl<'t, 'g> ConstraintSystem for Verifier<'t, 'g> {
    fn transcript(&mut self) -> &mut Transcript {
        self.transcript
    }

    fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    fn num_multipliers(&self) -> usize {
        self.num_vars
    }

    fn get_weights(&self) -> CircuitWeights {
        // Extract sparse-reduced weights from each constraint to construct the matrices
        let (w_l, w_r, w_o, w_v, c) = self
            // It's important that this iteration is in the correct order of the constraints,
            // otherwise we'll write the wrong index for the given constant in a constraint
            .constraints
            .iter()
            .enumerate()
            .map(|(i, lc)| {
                let (w_l_row, w_r_row, w_o_row, w_v_row, c_i) = lc.extract_weights();
                (w_l_row, w_r_row, w_o_row, w_v_row, (i, c_i))
            })
            .multiunzip();

        CircuitWeights {
            w_l,
            w_r,
            w_o,
            w_v,
            c,
        }
    }

    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        let var = self.num_vars;
        self.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        // Constrain l,r,o:
        left.add_term(l_var, -Scalar::one());
        right.add_term(r_var, -Scalar::one());
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate(&mut self, _: Option<Scalar>) -> Result<Variable, R1CSError> {
        match self.pending_multiplier {
            None => {
                let i = self.num_vars;
                self.num_vars += 1;
                self.pending_multiplier = Some(i);
                Ok(Variable::MultiplierLeft(i))
            }
            Some(i) => {
                self.pending_multiplier = None;
                Ok(Variable::MultiplierRight(i))
            }
        }
    }

    fn allocate_multiplier(
        &mut self,
        _: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        let var = self.num_vars;
        self.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        Ok((l_var, r_var, o_var))
    }

    fn commit_public(&mut self, value: Scalar) -> Variable {
        // Generate a pedersen commitment to the value
        let blinding_factor = Scalar::one();
        let commitment = self.pc_gens.commit(value, blinding_factor);

        // Forward the commitment to the existing method for ingesting pre-committed values
        self.commit(commitment)
    }

    fn constrain(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination
        // evals to 0 for prover, etc).
        self.constraints.push(lc);
    }

    fn eval(&self, _: &LinearCombination) -> Scalar {
        // Dummy value, at verification time this method may be called by a circuit
        // reconstructing an implicit constraint from the underlying assignment.
        // However, all that is needed for correct verification is that some variable
        // is allocated, not any specific value (these come from the proof itself)
        Scalar::zero()
    }
}

impl<'t, 'g> RandomizableConstraintSystem for Verifier<'t, 'g> {
    type RandomizedCS = RandomizingVerifier<'t, 'g>;

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        F: 'static + Fn(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        self.deferred_constraints.push(Box::new(callback));
        Ok(())
    }
}

impl<'t, 'g> ConstraintSystem for RandomizingVerifier<'t, 'g> {
    fn transcript(&mut self) -> &mut Transcript {
        self.verifier.transcript
    }

    fn num_constraints(&self) -> usize {
        self.verifier.num_constraints()
    }

    fn num_multipliers(&self) -> usize {
        self.verifier.num_multipliers()
    }

    fn get_weights(&self) -> CircuitWeights {
        self.verifier.get_weights()
    }

    fn multiply(
        &mut self,
        left: LinearCombination,
        right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        self.verifier.multiply(left, right)
    }

    fn allocate(&mut self, assignment: Option<Scalar>) -> Result<Variable, R1CSError> {
        self.verifier.allocate(assignment)
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(Scalar, Scalar)>,
    ) -> Result<(Variable, Variable, Variable), R1CSError> {
        self.verifier.allocate_multiplier(input_assignments)
    }

    fn commit_public(&mut self, value: Scalar) -> Variable {
        self.verifier.commit_public(value)
    }

    fn constrain(&mut self, lc: LinearCombination) {
        self.verifier.constrain(lc)
    }

    fn eval(&self, lc: &LinearCombination) -> Scalar {
        self.verifier.eval(lc)
    }
}

impl<'t, 'g> RandomizedConstraintSystem for RandomizingVerifier<'t, 'g> {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.verifier.transcript.challenge_scalar(label)
    }
}

impl<'t, 'g> Verifier<'t, 'g> {
    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `transcript` parameter is a Merlin proof transcript.  The
    /// `VerifierCS` holds onto the `&mut Transcript` until it consumes
    /// itself during [`VerifierCS::verify`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `VerifierCS` before proving is complete.
    ///
    /// The `commitments` parameter is a list of Pedersen commitments
    /// to the external variables for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a tuple `(cs, vars)`.
    ///
    /// The first element is the newly constructed constraint system.
    ///
    /// The second element is a list of [`Variable`]s corresponding to
    /// the external inputs, which can be used to form constraints.
    pub fn new(pc_gens: &'g PedersenGens, transcript: &'t mut Transcript) -> Self {
        transcript.r1cs_domain_sep();

        Verifier {
            transcript,
            pc_gens,
            num_vars: 0,
            V: Vec::new(),
            constraints: Vec::new(),
            deferred_constraints: Vec::new(),
            pending_multiplier: None,
        }
    }

    /// Creates commitment to a high-level variable and adds it to the transcript.
    ///
    /// # Inputs
    ///
    /// The `commitment` parameter is a Pedersen commitment
    /// to the external variable for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a pair of a Pedersen commitment (as a compressed Ristretto point),
    /// and a [`Variable`] corresponding to it, which can be used to form constraints.
    pub fn commit(&mut self, commitment: StarkPoint) -> Variable {
        let i = self.V.len();
        self.V.push(commitment);

        // Add the commitment to the transcript.
        self.transcript.append_point(b"V", &commitment);

        Variable::Committed(i)
    }

    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV, wc)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    ///
    /// This has the same logic as `ProverCS::flattened_constraints()`
    /// but also computes the constant terms (which the prover skips
    /// because they're not needed to construct the proof).
    pub fn flattened_constraints(
        &mut self,
        z: &Scalar,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar) {
        let n = self.num_vars;
        let m = self.V.len();

        let mut wL = vec![Scalar::zero(); n];
        let mut wR = vec![Scalar::zero(); n];
        let mut wO = vec![Scalar::zero(); n];
        let mut wV = vec![Scalar::zero(); m];
        let mut wc = Scalar::zero();

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::MultiplierLeft(i) => {
                        wL[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierRight(i) => {
                        wR[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierOutput(i) => {
                        wO[*i] += exp_z * coeff;
                    }
                    Variable::Committed(i) => {
                        wV[*i] -= exp_z * coeff;
                    }
                    Variable::One() => {
                        wc -= exp_z * coeff;
                    }
                    Variable::Zero() => {}
                }
            }
            exp_z *= *z;
        }

        (wL, wR, wO, wV, wc)
    }

    /// Calls all remembered callbacks with an API that
    /// allows generating challenge scalars.
    fn create_randomized_constraints(mut self) -> Result<Self, R1CSError> {
        // Clear the pending multiplier (if any) because it was committed into A_L/A_R/S.
        self.pending_multiplier = None;

        if self.deferred_constraints.is_empty() {
            self.transcript.r1cs_1phase_domain_sep();
            Ok(self)
        } else {
            self.transcript.r1cs_2phase_domain_sep();
            // Note: the wrapper could've used &mut instead of ownership,
            // but specifying lifetimes for boxed closures is not going to be nice,
            // so we move the self into wrapper and then move it back out afterwards.
            let mut callbacks = std::mem::take(&mut self.deferred_constraints);
            let mut wrapped_self = RandomizingVerifier { verifier: self };
            for callback in callbacks.drain(..) {
                callback(&mut wrapped_self)?;
            }
            Ok(wrapped_self.verifier)
        }
    }

    /// Consume this `VerifierCS` and attempt to verify the supplied `proof`.
    /// The `pc_gens` and `bp_gens` are generators for Pedersen commitments and
    /// Bulletproofs vector commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    pub fn verify(mut self, proof: &R1CSProof, bp_gens: &BulletproofGens) -> Result<(), R1CSError> {
        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.transcript.append_u64(b"m", self.V.len() as u64);

        let n1 = self.num_vars;
        self.transcript
            .validate_and_append_point(b"A_I1", &proof.A_I1)?;
        self.transcript
            .validate_and_append_point(b"A_O1", &proof.A_O1)?;
        self.transcript
            .validate_and_append_point(b"S1", &proof.S1)?;

        // Process the remaining constraints.
        self = self.create_randomized_constraints()?;

        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let n = self.num_vars;
        let n2 = n - n1;
        let padded_n = self.num_vars.next_power_of_two();
        let pad = padded_n - n;

        use crate::inner_product_proof::inner_product;
        use crate::util;
        use std::iter;

        if bp_gens.gens_capacity < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }
        // We are performing a single-party circuit proof, so party index is 0.
        let gens = bp_gens.share(0);

        // These points are the identity in the 1-phase un-randomized case.
        self.transcript.append_point(b"A_I2", &proof.A_I2);
        self.transcript.append_point(b"A_O2", &proof.A_O2);
        self.transcript.append_point(b"S2", &proof.S2);

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        self.transcript
            .validate_and_append_point(b"T_1", &proof.T_1)?;
        self.transcript
            .validate_and_append_point(b"T_3", &proof.T_3)?;
        self.transcript
            .validate_and_append_point(b"T_4", &proof.T_4)?;
        self.transcript
            .validate_and_append_point(b"T_5", &proof.T_5)?;
        self.transcript
            .validate_and_append_point(b"T_6", &proof.T_6)?;

        let u = self.transcript.challenge_scalar(b"u");
        let x = self.transcript.challenge_scalar(b"x");

        self.transcript.append_scalar(b"t_x", &proof.t_x);
        self.transcript
            .append_scalar(b"t_x_blinding", &proof.t_x_blinding);
        self.transcript
            .append_scalar(b"e_blinding", &proof.e_blinding);

        let w = self.transcript.challenge_scalar(b"w");

        let (wL, wR, wO, wV, wc) = self.flattened_constraints(&z);

        // Get IPP variables
        let (u_sq, u_inv_sq, s) = proof
            .ipp_proof
            .verification_scalars(padded_n, self.transcript)
            .map_err(|_| R1CSError::VerificationError)?;

        let a = proof.ipp_proof.a;
        let b = proof.ipp_proof.b;

        let y_inv = y.inverse();
        let y_inv_vec = util::exp_iter(y_inv)
            .take(padded_n)
            .collect::<Vec<Scalar>>();
        let yneg_wR = wR
            .into_iter()
            .zip(y_inv_vec.iter())
            .map(|(wRi, exp_y_inv)| wRi * exp_y_inv)
            .chain(iter::repeat(Scalar::zero()).take(pad))
            .collect::<Vec<Scalar>>();

        let delta = inner_product(&yneg_wR[0..n], &wL);

        let u_for_g = iter::repeat(Scalar::one())
            .take(n1)
            .chain(iter::repeat(u).take(n2 + pad));
        let u_for_h = u_for_g.clone();

        // define parameters for P check
        let g_scalars = yneg_wR
            .iter()
            .zip(u_for_g)
            .zip(s.iter().take(padded_n))
            .map(|((yneg_wRi, u_or_1), s_i)| u_or_1 * (x * yneg_wRi - a * s_i));

        let h_scalars = y_inv_vec
            .iter()
            .zip(u_for_h)
            .zip(s.iter().rev().take(padded_n))
            .zip(wL.into_iter().chain(iter::repeat(Scalar::zero()).take(pad)))
            .zip(wO.into_iter().chain(iter::repeat(Scalar::zero()).take(pad)))
            .map(|((((y_inv_i, u_or_1), s_i_inv), wLi), wOi)| {
                u_or_1 * (y_inv_i * (x * wLi + wOi - b * s_i_inv) - Scalar::one())
            });

        // Create a `TranscriptRng` from the transcript. The verifier
        // has no witness data to commit, so this just mixes external
        // randomness into the existing transcript.
        let r = self.transcript.challenge_scalar(b"r");

        let xx = x * x;
        let rxx = r * xx;
        let xxx = x * xx;

        // group the T_scalars and T_points together
        let T_scalars = [r * x, rxx * x, rxx * xx, rxx * xxx, rxx * xx * xx];
        let T_points = [proof.T_1, proof.T_3, proof.T_4, proof.T_5, proof.T_6];

        let mega_check = StarkPoint::msm_iter(
            iter::once(x) // A_I1
                .chain(iter::once(xx)) // A_O1
                .chain(iter::once(xxx)) // S1
                .chain(iter::once(u * x)) // A_I2
                .chain(iter::once(u * xx)) // A_O2
                .chain(iter::once(u * xxx)) // S2
                .chain(wV.iter().map(|wVi| wVi * rxx)) // V
                .chain(T_scalars.iter().cloned()) // T_points
                .chain(iter::once(
                    w * (proof.t_x - a * b) + r * (xx * (wc + delta) - proof.t_x),
                )) // B
                .chain(iter::once(-proof.e_blinding - r * proof.t_x_blinding)) // B_blinding
                .chain(g_scalars) // G
                .chain(h_scalars) // H
                .chain(u_sq.iter().cloned()) // ipp_proof.L_vec
                .chain(u_inv_sq.iter().cloned()), // ipp_proof.R_vec
            iter::once(proof.A_I1)
                .chain(iter::once(proof.A_O1))
                .chain(iter::once(proof.S1))
                .chain(iter::once(proof.A_I2))
                .chain(iter::once(proof.A_O2))
                .chain(iter::once(proof.S2))
                .chain(self.V.into_iter())
                .chain(T_points.into_iter())
                .chain(iter::once(self.pc_gens.B))
                .chain(iter::once(self.pc_gens.B_blinding))
                .chain(gens.G(padded_n).copied())
                .chain(gens.H(padded_n).copied())
                .chain(proof.ipp_proof.L_vec.iter().copied())
                .chain(proof.ipp_proof.R_vec.iter().copied()),
        );

        if !mega_check.is_identity() {
            return Err(R1CSError::VerificationError);
        }

        Ok(())
    }
}
