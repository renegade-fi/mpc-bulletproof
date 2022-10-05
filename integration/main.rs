//! Integration test harness, largely borrowed from:
//!     https://github.com/renegade-fi/MPC-Ristretto
#![cfg(feature = "integration_test")]

mod mpc_inner_product;

use std::{borrow::Borrow, cell::RefCell, net::SocketAddr, process::exit, rc::Rc};

use clap::Parser;
use colored::Colorize;
use curve25519_dalek::scalar::Scalar;
use dns_lookup::lookup_host;

use mpc_ristretto::beaver::SharedValueSource;
use mpc_ristretto::fabric::AuthenticatedMpcFabric;
use mpc_ristretto::network::{MpcNetwork, QuicTwoPartyNet};

type SharedMpcFabric = Rc<RefCell<AuthenticatedMpcFabric<QuicTwoPartyNet, PartyIDBeaverSource>>>;

/// Integration test arguments, common to all tests
#[derive(Clone, Debug)]
#[allow(dead_code)]
struct IntegrationTestArgs {
    party_id: u64,
    mpc_fabric: Rc<RefCell<AuthenticatedMpcFabric<QuicTwoPartyNet, PartyIDBeaverSource>>>,
}

/// Integration test format
#[derive(Clone)]
struct IntegrationTest {
    pub name: &'static str,
    pub test_fn: fn(&IntegrationTestArgs) -> Result<(), String>,
}

// Collect the statically defined tests into an interable
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
impl SharedValueSource<Scalar> for PartyIDBeaverSource {
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
}

#[allow(unused_doc_comments, clippy::await_holding_refcell_ref)]
#[tokio::main]
async fn main() {
    /**
     * Setup
     */
    let args = Args::parse();

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

    net.connect().await.unwrap();

    // Share the global mac key (hardcoded to Scalar(15))
    let net_ref = Rc::new(RefCell::new(net));
    let beaver_source = Rc::new(RefCell::new(PartyIDBeaverSource::new(args.party)));

    let mpc_fabric = Rc::new(RefCell::new(AuthenticatedMpcFabric::new_with_network(
        args.party,
        net_ref.clone(),
        beaver_source,
    )));

    /**
     * Test harness
     */
    if args.party == 0 {
        println!("\n\n{}\n", "Running integration tests...".blue());
    }

    let test_args = IntegrationTestArgs {
        party_id: args.party,
        mpc_fabric,
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

    // Close the network
    #[allow(clippy::await_holding_refcell_ref, unused_must_use)]
    if net_ref.as_ref().borrow_mut().close().await.is_err() {
        println!("Error tearing down connection");
    }

    if all_success {
        if args.party == 0 {
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
