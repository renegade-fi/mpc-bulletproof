#![allow(non_snake_case)]

use rand::Rng;
use itertools::Itertools;
use mpc_bulletproof::{BulletproofGens, PedersenGens, r1cs_mpc::{
    PartiallySharedR1CSProof,
    MpcRandomizableConstraintSystem,
    MpcRandomizedConstraintSystem,
    MpcConstraintSystem,
    MpcVariable,
    MpcProver,
    MpcLinearCombination,
    MultiproverError},

};
use mpc_stark::algebra::authenticated_stark_point::AuthenticatedStarkPointOpenResult;
use rand::seq::SliceRandom;
use rand::{thread_rng};
use merlin::HashChainTranscript as Transcript;
use mpc_stark::{
    algebra::scalar::Scalar, beaver::SharedValueSource, network::{MpcNetwork}, MpcFabric, PARTY0, PARTY1,
};
use mpc_stark::error::MpcNetworkError;
use std::{
    pin::Pin,
    task::{Context, Poll},
};

use tokio::sync::mpsc::{unbounded_channel, UnboundedReceiver, UnboundedSender};

use mpc_stark::network::NetworkOutbound;

use mpc_stark::network::PartyId;
use futures::{Future, Sink, Stream};
use async_trait::async_trait;
use futures::future::join_all;
use mpc_bulletproof::{
    r1cs::{
        ConstraintSystem, R1CSError, RandomizableConstraintSystem, RandomizedConstraintSystem,
        Variable, Verifier,
    },
};



/// An implementation of a beaver value source that returns
/// beaver triples (0, 0, 0) for party 0 and (1, 1, 1) for party 1
#[derive(Clone, Debug, Default)]
pub struct PartyIDBeaverSource {
    /// The ID of the local party
    party_id: u64,
}

impl PartyIDBeaverSource {
    /// Create a new beaver source given the local party_id
    pub fn new(party_id: u64) -> Self {
        Self { party_id }
    }
}

/// The PartyIDBeaverSource returns beaver triplets split statically between the
/// parties. We assume a = 2, b = 3 ==> c = 6. [a] = (1, 1); [b] = (3, 0) [c] = (2, 4)
impl SharedValueSource for PartyIDBeaverSource {
    fn next_shared_bit(&mut self) -> Scalar {
        // Simply output partyID, assume partyID \in {0, 1}
        assert!(self.party_id == 0 || self.party_id == 1);
        Scalar::from(self.party_id)
    }

    fn next_triplet(&mut self) -> (Scalar, Scalar, Scalar) {
        if self.party_id == 0 {
            (Scalar::from(1u64), Scalar::from(3u64), Scalar::from(2u64))
        } else {
            (Scalar::from(1u64), Scalar::from(0u64), Scalar::from(4u64))
        }
    }

    fn next_shared_inverse_pair(&mut self) -> (Scalar, Scalar) {
        (Scalar::from(self.party_id), Scalar::from(self.party_id))
    }

    fn next_shared_value(&mut self) -> Scalar {
        Scalar::from(self.party_id)
    }
}

/// A dummy MPC network that operates over a duplex channel instead of a network connection/// An unbounded duplex channel used to mock a network connection
pub struct UnboundedDuplexStream {
    /// The send side of the stream
    send: UnboundedSender<NetworkOutbound>,
    /// The receive side of the stream
    recv: UnboundedReceiver<NetworkOutbound>,
}

impl UnboundedDuplexStream {
    /// Create a new pair of duplex streams
    pub fn new_duplex_pair() -> (Self, Self) {
        let (send1, recv1) = unbounded_channel();
        let (send2, recv2) = unbounded_channel();

        (
            Self {
                send: send1,
                recv: recv2,
            },
            Self {
                send: send2,
                recv: recv1,
            },
        )
    }

    /// Send a message on the stream
    pub fn send(&mut self, msg: NetworkOutbound) {
        self.send.send(msg).unwrap();
    }

    /// Recv a message from the stream
    pub async fn recv(&mut self) -> NetworkOutbound {
        self.recv.recv().await.unwrap()
    }
}


/// A dummy network implementation used for unit testing
pub struct MockNetwork {
    /// The ID of the local party
    party_id: PartyId,
    /// The underlying mock network connection
    mock_conn: UnboundedDuplexStream,
}

impl MockNetwork {
    /// Create a new mock network from one half of a duplex stream
    pub fn new(party_id: PartyId, stream: UnboundedDuplexStream) -> Self {
        Self {
            party_id,
            mock_conn: stream,
        }
    }
}

#[async_trait]
impl MpcNetwork for MockNetwork {
    fn party_id(&self) -> PartyId {
        self.party_id
    }

    async fn close(&mut self) -> Result<(), MpcNetworkError> {
        Ok(())
    }
}

impl Stream for MockNetwork {
    type Item = Result<NetworkOutbound, MpcNetworkError>;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        Box::pin(self.mock_conn.recv())
            .as_mut()
            .poll(cx)
            .map(|value| Some(Ok(value)))
    }
}

impl Sink<NetworkOutbound> for MockNetwork {
    type Error = MpcNetworkError;

    fn poll_ready(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn start_send(mut self: Pin<&mut Self>, item: NetworkOutbound) -> Result<(), Self::Error> {
        self.mock_conn.send(item);
        Ok(())
    }

    fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn poll_close(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }
}

pub async fn execute_mock_mpc<T, S, F>(mut f: F) -> (T, T)
where
    T: Send + 'static,
S: Future<Output = T> + Send + 'static,
F: FnMut(MpcFabric) -> S,
{
    // Build a duplex stream to broker communication between the two parties
    let (party0_stream, party1_stream) = UnboundedDuplexStream::new_duplex_pair();
    let party0_fabric = MpcFabric::new(
        MockNetwork::new(PARTY0, party0_stream),
        PartyIDBeaverSource::new(PARTY0),
    );
    let party1_fabric = MpcFabric::new(
        MockNetwork::new(PARTY1, party1_stream),
        PartyIDBeaverSource::new(PARTY1),
    );

    // Spawn two tasks to execute the MPC
    let fabric0 = party0_fabric.clone();
    let fabric1 = party1_fabric.clone();
    let party0_task = tokio::spawn(f(fabric0));
    let party1_task = tokio::spawn(f(fabric1));

    let party0_output = party0_task.await.unwrap();
    let party1_output = party1_task.await.unwrap();

    // Shutdown the fabrics
    party0_fabric.shutdown();
    party1_fabric.shutdown();

    (party0_output, party1_output)
}

// Shuffle gadget (documented in markdown file)

/// A proof-of-shuffle.
struct MpcShuffleProof(PartiallySharedR1CSProof);

impl MpcShuffleProof {
    fn gadget<CS: MpcRandomizableConstraintSystem>(
        cs: &mut CS,
        x: Vec<MpcVariable>,
        y: Vec<MpcVariable>,
    ) -> Result<(), R1CSError> {
        assert_eq!(x.len(), y.len());
        let k = x.len();

        if k == 1 {
            cs.constrain(&y[0] - &x[0]);
            return Ok(());
        }

        cs.specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"shuffle challenge");

            // Make last x multiplier for i = k-1 and k-2
            let Ok((_, _, last_mulx_out)) = cs.multiply(&(&x[k - 1] - &z), &(&x[k - 2] - &z)) else { todo!() };

            // Make multipliers for x from i == [0, k-3]
            let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |prev_out, i| {
                let Ok((_, _, o)) = cs.multiply(&MpcLinearCombination::from(prev_out), &(&x[i] - &z)) else { todo!() };
                o
            });

            // Make last y multiplier for i = k-1 and k-2
            let Ok((_, _, last_muly_out)) = cs.multiply(&(&y[k - 1] - &z), &(&y[k - 2] - &z)) else { todo!() };

            // Make multipliers for y from i == [0, k-3]
            let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |prev_out, i| {
                let Ok((_, _, o)) = cs.multiply(&MpcLinearCombination::from(prev_out), &(&y[i] - &z)) else { todo!() };
                o
            });

            // Constrain last x mul output and last y mul output to be equal
            cs.constrain(first_mulx_out - first_muly_out);

            Ok(())
        })
    }
}

impl MpcShuffleProof {
    /// Attempt to construct a proof that `output` is a permutation of `input`.
    ///
    /// Returns a tuple `(proof, input_commitments || output_commitments)`.
    pub fn prove(
        fabric: MpcFabric,
        pc_gens: PedersenGens,
        bp_gens: &BulletproofGens,
        mut transcript: Transcript,
        input: &[Scalar],
        output: &[Scalar],
    ) -> Result<(MpcShuffleProof, Vec<AuthenticatedStarkPointOpenResult>, Vec<AuthenticatedStarkPointOpenResult>), String> {
        let mut rng = thread_rng();
        let k = input.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_u64(b"k", k as u64);

        let mut prover = MpcProver::new_with_fabric(fabric, transcript, pc_gens);

        // Commit to the inputs
        let (input_commit, input_vars) = prover
            .batch_commit(
                PARTY0,
                input.iter().copied(),
                &(0..input.len()).map(|_| Scalar::random(&mut rng)).collect_vec(),
            )
            .map_err(|err| format!("Error committing to `input` values: {:?}", err))?;

        let (output_commit, output_vars) = prover
            .batch_commit(
                PARTY1,
                output.iter().copied(),
                &(0..output.len()).map(|_| Scalar::random(&mut rng)).collect_vec(),
            )
            .map_err(|err| format!("Error committing to `output` values: {:?}", err))?;

        // Apply the gadget to specify the constraints and prove the statement
        Self::gadget(&mut prover, input_vars.clone(), output_vars.clone())
            .map_err(|err| format!("Error specifying constraints: {:?}", err))?;

        let proof = prover
            .prove(&bp_gens)
            .map_err(|err| format!("Error proving: {:?}", err))?;

        Ok((MpcShuffleProof(proof), input_commit, output_commit))
    }
}


impl MpcShuffleProof {

    fn single_prover_gadget<CS: RandomizableConstraintSystem>(
        cs: &mut CS,
        x: Vec<Variable>,
        y: Vec<Variable>,
    ) -> Result<(), R1CSError> {
        assert_eq!(x.len(), y.len());
        let k = x.len();

        if k == 1 {
            cs.constrain(y[0] - x[0]);
            return Ok(());
        }

        cs.specify_randomized_constraints(move |cs| {
            let z = cs.challenge_scalar(b"shuffle challenge");
            let (_, _, last_mulx_out) = cs.multiply(x[k - 1] - z, x[k - 2] - z);
            let first_mulx_out = (0..k - 2).rev().fold(last_mulx_out, |acc, i| {
                let (_, _, o) = cs.multiply(acc.into(), x[i] - z);
                o
            });

            let (_, _, last_muly_out) = cs.multiply(y[k - 1] - z, y[k - 2] - z);
            let first_muly_out = (0..k - 2).rev().fold(last_muly_out, |acc, i| {
                let (_, _, o) = cs.multiply(acc.into(), y[i] - z);
                o
            });

            cs.constrain(first_mulx_out - first_muly_out);

            Ok(())
        })?;

        Ok(())
    }

    /// Attempt to verify a `ShuffleProof`.
    pub async fn verify(
        &self,
        pc_gens: &PedersenGens,
        bp_gens: &BulletproofGens,
        transcript: &mut Transcript,
        input_commitments: Vec<AuthenticatedStarkPointOpenResult>,
        output_commitments: Vec<AuthenticatedStarkPointOpenResult>,
    ) -> Result<(), MultiproverError> {
        let k = input_commitments.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_u64(b"k", k as u64);

        let opened_proof = self.0.open().await?;
        let input_commitments_starkpoint = join_all(input_commitments)
            .await
            .into_iter()
            .collect::<Result<Vec<_>, _>>()
            .map_err(MultiproverError::Mpc)?;
        let output_commitments_starkpoint = join_all(output_commitments)
            .await
            .into_iter()
            .collect::<Result<Vec<_>, _>>()
            .map_err(MultiproverError::Mpc)?;

        let mut verifier = Verifier::new(pc_gens, transcript);

        let input_vars = input_commitments_starkpoint
            .iter().map(|V| verifier.commit(*V)).collect_vec();
        let output_vars = output_commitments_starkpoint
            .iter().map(|V| verifier.commit(*V)).collect_vec();

        Self::single_prover_gadget(&mut verifier, input_vars, output_vars)
            .map_err(MultiproverError::ProverError)?;
        verifier.verify(&opened_proof, bp_gens)
            .map_err(MultiproverError::ProverError)

    }
}


#[tokio::test]
async fn mpc_shuffle_proof_test() {
    let k: usize = 2;
    let (_, _) = execute_mock_mpc(|fabric| async  move {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new((2 * k).next_power_of_two(), 1);

        let (proof, input_commitments, output_commitments) = {
            // Randomly generate inputs and outputs to kshuffle
            let mut rng = rand::thread_rng();
            let (min, max) = (0u64, std::u64::MAX);
            let input: Vec<Scalar> = (0..k)
                .map(|_| Scalar::from(rng.gen_range(min..max)))
                .collect();
            let mut output = input.clone();
            output.shuffle(&mut rand::thread_rng());

            let prover_transcript = Transcript::new(b"ShuffleProofTest");
            MpcShuffleProof::prove(fabric.clone(), pc_gens, &bp_gens, prover_transcript, &input, &output).unwrap()
        };

        let mut verifier_transcript = Transcript::new(b"ShuffleProofTest");
        proof.verify(
            &pc_gens,
            &bp_gens,
            &mut verifier_transcript,
            input_commitments,
            output_commitments
        ).await.err()
            .map(|err| {
                if let MultiproverError::ProverError(R1CSError::VerificationError) = err {
                    Ok(())
                } else {
                    Err(format!("Expected verification error, got {:?}", err))
                }
            })
            .unwrap_or(Err("Expected verification error, got Ok".to_string()))
    }).await;
}
