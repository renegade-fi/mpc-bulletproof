//! Integration test harness, largely borrowed from:
//!     https://github.com/renegade-fi/MPC-Ristretto
#![cfg(feature = "integration_test")]

mod mpc_inner_product;
mod mpc_prover;

use std::{borrow::Borrow, net::SocketAddr, process::exit};

use clap::Parser;
use colored::Colorize;
use dns_lookup::lookup_host;
use mpc_stark::{
    algebra::scalar::Scalar, beaver::SharedValueSource, fabric::MpcFabric, network::QuicTwoPartyNet,
};
use tokio::runtime::{Builder as RuntimeBuilder, Handle};

/// The amount of time to await the executor shutting down
const SHUTDOWN_TIMEOUT: u64 = 1000;

/// Integration test arguments, common to all tests
#[derive(Clone, Debug)]
#[allow(dead_code)]
struct IntegrationTestArgs {
    party_id: u64,
    mpc_fabric: MpcFabric,
}

/// Integration test format
#[derive(Clone)]
struct IntegrationTest {
    pub name: &'static str,
    pub test_fn: fn(&IntegrationTestArgs) -> Result<(), String>,
}

// Collect the statically defined tests into an iterable
inventory::collect!(IntegrationTest);

/// The command line interface for the test harness
#[derive(Parser, Debug)]
struct Args {
    /// The party id of the
    #[clap(long, value_parser)]
    party: u64,
    /// The port to accept inbound on
    #[clap(long = "port1", value_parser)]
    port1: u64,
    /// The port to expect the counterparty on
    #[clap(long = "port2", value_parser)]
    port2: u64,
    /// The test to run
    #[clap(short, long, value_parser)]
    test: Option<String>,
    /// Whether running in docker or not, used for peer lookup
    #[clap(long, takes_value = false, value_parser)]
    docker: bool,
}

/// A dummy beaver triplet source used in the integration test.
/// Beaver sources are an infra concern, and this library will transparently
/// take them as a parameter and pass them down the stack.
/// Returns beaver triples (0, 0, 0) for party 0 and (1, 1, 1) for party 1
#[derive(Debug)]
pub(crate) struct PartyIDBeaverSource {
    party_id: u64,
}

impl PartyIDBeaverSource {
    pub fn new(party_id: u64) -> Self {
        Self { party_id }
    }
}

/// The PartyIDBeaverSource returns beaver triplets split statically between the
/// parties. We assume a = 2, b = 3 ==> c = 6. [a] = (1, 1); [b] = (3, 0) [c] = (2, 4)
impl SharedValueSource for PartyIDBeaverSource {
    fn next_triplet(&mut self) -> (Scalar, Scalar, Scalar) {
        if self.party_id == 0 {
            (Scalar::from(1u64), Scalar::from(3u64), Scalar::from(2u64))
        } else {
            (Scalar::from(1u64), Scalar::from(0u64), Scalar::from(4u64))
        }
    }

    fn next_shared_value(&mut self) -> Scalar {
        Scalar::from(self.party_id)
    }

    fn next_shared_bit(&mut self) -> Scalar {
        Scalar::from(self.party_id)
    }

    fn next_shared_inverse_pair(&mut self) -> (Scalar, Scalar) {
        (Scalar::from(2u64), Scalar::from(2u64).inverse())
    }
}

#[allow(unused_doc_comments, clippy::await_holding_refcell_ref)]
fn main() {
    // ---------
    // | Setup |
    // ---------

    let args = Args::parse();
    let party_id = args.party;

    // Build a runtime to execute within
    let runtime = RuntimeBuilder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap();

    let result = runtime.spawn_blocking(move || {
        // Listen on 0.0.0.0 (all network interfaces) with the given port
        // We do this because listening on localhost when running in a container points to
        // the container's loopback interface, not the docker bridge
        let local_addr: SocketAddr = format!("0.0.0.0:{}", args.port1).parse().unwrap();

        // If the code is running in a docker compose setup (set by the --docker flag); attempt
        // to lookup the peer via DNS. The compose networking interface will add an alias for
        // party0 for the first peer and party1 for the second.
        // If not running on docker, dial the peer directly on the loopback interface.
        let peer_addr: SocketAddr = {
            if args.docker {
                let other_host_alias = format!("party{}", if args.party == 1 { 0 } else { 1 });
                let hosts = lookup_host(other_host_alias.as_str()).unwrap();

                println!(
                    "Lookup successful for {}... found hosts: {:?}",
                    other_host_alias, hosts
                );

                format!("{}:{}", hosts[0], args.port2).parse().unwrap()
            } else {
                format!("{}:{}", "127.0.0.1", args.port2).parse().unwrap()
            }
        };

        println!("Lookup successful, found peer at {:?}", peer_addr);

        // Build and connect to the network
        let mut net = QuicTwoPartyNet::new(args.party, local_addr, peer_addr);

        Handle::current().block_on(net.connect()).unwrap();

        // Share the global mac key (hardcoded to Scalar(15))
        let beaver_source = PartyIDBeaverSource::new(args.party);
        let fabric = MpcFabric::new(net, beaver_source);

        // ----------------
        // | Test Harness |
        // ----------------

        if args.party == 0 {
            println!("\n\n{}\n", "Running integration tests...".blue());
        }

        let test_args = IntegrationTestArgs {
            party_id: args.party,
            mpc_fabric: fabric.clone(),
        };

        let mut all_success = true;

        for test in inventory::iter::<IntegrationTest> {
            if args.borrow().test.is_some() && args.borrow().test.as_deref().unwrap() != test.name {
                continue;
            }

            if args.party == 0 {
                print!("Running {}... ", test.name);
            }
            let res: Result<(), String> = (test.test_fn)(&test_args);
            all_success &= validate_success(res, args.party);
        }

        // Shutdown the fabric and await its termination
        #[allow(clippy::await_holding_refcell_ref, unused_must_use)]
        fabric.shutdown();
        Handle::current().block_on(tokio::time::sleep(tokio::time::Duration::from_millis(
            SHUTDOWN_TIMEOUT,
        )));

        all_success
    });

    let all_success = runtime.block_on(result).unwrap();
    if all_success {
        if party_id == 0 {
            println!("\n{}", "Integration tests successful!".green(),);
        }

        exit(0);
    }

    exit(-1);
}

/// Prints a success or failure message, returns true if success, false if failure
#[inline]
fn validate_success(res: Result<(), String>, party_id: u64) -> bool {
    if res.is_ok() {
        if party_id == 0 {
            println!("{}", "Success!".green());
        }

        true
    } else {
        println!("{}\n\t{}", "Failure...".red(), res.err().unwrap());
        false
    }
}
