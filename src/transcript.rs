//! Defines a `TranscriptProtocol` trait for using a Merlin transcript.

use std::sync::Arc;
use std::sync::Mutex;

use merlin::{pad_label, HashChainTranscript};
use mpc_stark::algebra::scalar::ScalarResult;
use mpc_stark::algebra::stark_curve::StarkPointResult;
use mpc_stark::algebra::{scalar::Scalar, stark_curve::StarkPoint};
use mpc_stark::MpcFabric;
use mpc_stark::ResultId;
use mpc_stark::ResultValue;

use crate::errors::ProofError;

/// The error thrown by `expect`s on the MPC transcript's lock
const ERR_LOCK_POISONED: &str = "transcript lock poisoned";

pub trait TranscriptProtocol {
    /// Append a domain separator for an `n`-bit, `m`-party range proof.
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64);

    /// Append a domain separator for a length-`n` inner product proof.
    fn innerproduct_domain_sep(&mut self, n: u64);

    /// Append a domain separator for a constraint system.
    fn r1cs_domain_sep(&mut self);

    /// Commit a domain separator for a CS without randomized constraints.
    fn r1cs_1phase_domain_sep(&mut self);

    /// Commit a domain separator for a CS with randomized constraints.
    fn r1cs_2phase_domain_sep(&mut self);

    /// Append a `scalar` with the given `label`.
    fn append_scalar(&mut self, label: &'static [u8], scalar: &Scalar);

    /// Append a `point` with the given `label`.
    fn append_point(&mut self, label: &'static [u8], point: &StarkPoint);

    /// Check that a point is not the identity, then append it to the
    /// transcript.  Otherwise, return an error.
    fn validate_and_append_point(
        &mut self,
        label: &'static [u8],
        point: &StarkPoint,
    ) -> Result<(), ProofError>;

    /// Compute a `label`ed challenge variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar;
}

// ----------------------------
// | Single Prover Transcript |
// ----------------------------

impl TranscriptProtocol for HashChainTranscript {
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64) {
        self.append_message(b"dom-sep", &pad_label(b"rangeproof v1"));
        self.append_u64(b"n", n);
        self.append_u64(b"m", m);
    }

    fn innerproduct_domain_sep(&mut self, n: u64) {
        self.append_message(b"dom-sep", &pad_label(b"ipp v1"));
        self.append_u64(b"n", n);
    }

    fn r1cs_domain_sep(&mut self) {
        self.append_message(b"dom-sep", &pad_label(b"r1cs v1"));
    }

    fn r1cs_1phase_domain_sep(&mut self) {
        self.append_message(b"dom-sep", &pad_label(b"r1cs-1phase"));
    }

    fn r1cs_2phase_domain_sep(&mut self) {
        self.append_message(b"dom-sep", &pad_label(b"r1cs-2phase"));
    }

    fn append_scalar(&mut self, label: &'static [u8], scalar: &Scalar) {
        // Reverse the scalar bytes so that it is absorbed into the transcript
        // in little-endian order, matching what is done in the Cairo implementation.
        let buf: Vec<u8> = scalar.to_bytes_be().iter().rev().cloned().collect();
        self.append_message(label, &buf);
    }

    fn append_point(&mut self, label: &'static [u8], point: &StarkPoint) {
        let buf = point.to_transcript_bytes();
        self.append_message(label, &buf);
    }

    /// Check that a point is not the identity, then append it to the
    /// transcript.  Otherwise, return an error.
    fn validate_and_append_point(
        &mut self,
        label: &'static [u8],
        point: &StarkPoint,
    ) -> Result<(), ProofError> {
        if point == &StarkPoint::identity() {
            Err(ProofError::VerificationError)
        } else {
            let buf = point.to_transcript_bytes();
            self.append_message(label, &buf);
            Ok(())
        }
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        let mut low_u256 = [0u8; STARK_POINT_BYTES];
        self.challenge_bytes(label, &mut low_u256);

        Scalar::from_uniform_bytes(low_u256)
    }
}

// ------------------
// | MPC Transcript |
// ------------------

/// A transcript used in a multiprover setting in which the results added to the
/// transcript are represented as promises to incomplete computation
///
/// This transcript uses the underlying MPC fabric to sequence accesses to the Merlin
/// transcript as results of inputs and outputs become available to the fabric
pub struct MpcTranscript {
    /// The underlying Merlin transcript
    transcript: Arc<Mutex<HashChainTranscript>>,
    /// The latest operation ID in the transcript, the next operation in the transcript
    /// will "virtually depend" on this operation to sequence itself behind the current op
    latest_op_id: ResultId,
    /// A reference to the underlying MPC fabric
    fabric: MpcFabric,
}

impl MpcTranscript {
    /// Constructor
    pub fn new(transcript: HashChainTranscript, fabric: MpcFabric) -> Self {
        Self {
            transcript: Arc::new(Mutex::new(transcript)),
            latest_op_id: ResultId::default(),
            fabric,
        }
    }

    /// Append a domain separator for an `n`-bit, `m`-party range proof.
    pub fn innerproduct_domain_sep(&mut self, n: u64) {
        let transcript_ref = self.transcript.clone();
        self.fabric
            .new_gate_op::<_, Scalar>(vec![self.latest_op_id], move |_args| {
                let mut locked_transcript = transcript_ref.lock().expect(ERR_LOCK_POISONED);
                locked_transcript.append_message(b"dom-sep", b"ipp v1");
                locked_transcript.append_u64(b"n", n);

                ResultValue::Scalar(Scalar::zero())
            });
    }

    /// Append a domain separator for a constraint system.
    pub fn r1cs_domain_sep(&mut self) {
        let transcript_ref = self.transcript.clone();
        self.fabric
            .new_gate_op::<_, Scalar>(vec![self.latest_op_id], move |_args| {
                let mut locked_transcript = transcript_ref.lock().expect(ERR_LOCK_POISONED);
                locked_transcript.append_message(b"dom-sep", b"r1cs v1");

                ResultValue::Scalar(Scalar::zero())
            });
    }

    /// Commit a domain separator for a CS without randomized constraints.
    pub fn r1cs_1phase_domain_sep(&mut self) {
        let transcript_ref = self.transcript.clone();
        self.fabric
            .new_gate_op::<_, Scalar>(vec![self.latest_op_id], move |_args| {
                let mut locked_transcript = transcript_ref.lock().expect(ERR_LOCK_POISONED);
                locked_transcript.append_message(b"dom-sep", b"r1cs-1phase");

                ResultValue::Scalar(Scalar::zero())
            });
    }

    /// Commit a domain separator for a CS with randomized constraints.
    pub fn r1cs_2phase_domain_sep(&mut self) {
        let transcript_ref = self.transcript.clone();
        self.fabric
            .new_gate_op::<_, Scalar>(vec![self.latest_op_id], move |_args| {
                let mut locked_transcript = transcript_ref.lock().expect(ERR_LOCK_POISONED);
                locked_transcript.append_message(b"dom-sep", b"r1cs-2phase");

                ResultValue::Scalar(Scalar::zero())
            });
    }

    /// Append a `u64` with the given label
    pub fn append_u64(&mut self, label: &'static [u8], value: u64) {
        let transcript_ref = self.transcript.clone();
        self.fabric
            .new_gate_op::<_, Scalar>(vec![self.latest_op_id], move |_args| {
                let mut locked_transcript = transcript_ref.lock().expect(ERR_LOCK_POISONED);
                locked_transcript.append_u64(label, value);

                ResultValue::Scalar(Scalar::zero())
            });
    }

    /// Append a `scalar` with the given `label`.
    pub fn append_scalar(&mut self, label: &'static [u8], scalar: &ScalarResult) {
        // Allocate a dummy operation that will be used to sequence the transcript, the result
        // is the identity, but has the side effect of updating the underlying strobe state
        // Further operations will "depend" on this operation so that they are sequenced behind it
        let mut dependencies = vec![self.latest_op_id];
        dependencies.append(&mut scalar.op_ids());

        let transcript_ref = self.transcript.clone();
        let op_res: ScalarResult = self.fabric.new_gate_op(dependencies, move |mut args| {
            // args[0] is unused, this is the dummy dependency
            let scalar_val: Scalar = args.remove(1).into();
            let mut locked_transcript = transcript_ref.lock().expect(ERR_LOCK_POISONED);
            locked_transcript.append_scalar(label, &scalar_val);

            ResultValue::Scalar(scalar_val)
        });

        self.latest_op_id = op_res.op_ids()[0];
    }

    /// Append a `point` with the given `label`.
    pub fn append_point(&mut self, label: &'static [u8], point: &StarkPointResult) {
        // As in `append_scalar` allocate a dummy op to sequence further operations behind
        let mut dependencies = vec![self.latest_op_id];
        dependencies.append(&mut point.op_ids());

        let transcript_ref = self.transcript.clone();
        let op_res: StarkPointResult = self.fabric.new_gate_op(dependencies, move |mut args| {
            // args[0] is unused, this is the dummy dependency
            let point_val: StarkPoint = args.remove(1).into();
            let mut locked_transcript = transcript_ref.lock().expect(ERR_LOCK_POISONED);
            locked_transcript.append_point(label, &point_val);

            ResultValue::Point(point_val)
        });

        self.latest_op_id = op_res.op_ids()[0];
    }

    /// Compute a `label`ed challenge variable.
    pub fn challenge_scalar(&mut self, label: &'static [u8]) -> ScalarResult {
        // As in `append_scalar` allocate a dummy op to sequence further operations behind
        let dependencies = vec![self.latest_op_id];

        let transcript_ref = self.transcript.clone();
        let op_res: ScalarResult = self.fabric.new_gate_op(dependencies, move |_args| {
            let mut locked_transcript = transcript_ref.lock().expect(ERR_LOCK_POISONED);
            let res = locked_transcript.challenge_scalar(label);

            ResultValue::Scalar(res)
        });

        self.latest_op_id = op_res.op_ids()[0];
        op_res
    }
}
