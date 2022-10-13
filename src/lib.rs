#![cfg_attr(not(feature = "std"), no_std)]
#![doc = include_str!("../README.md")]
#![feature(try_trait_v2)]
// #![deny(missing_docs)]
#![doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")]
#![doc(html_root_url = "https://docs.rs/bulletproofs/2.0.0")]

extern crate alloc;

#[macro_use]
extern crate serde_derive;

// Publically export utils for testing, but not otherwise
#[cfg(not(feature = "integration_test"))]
mod util;
#[allow(missing_docs)]
#[cfg(feature = "integration_test")]
pub mod util;

#[doc = include_str!("../docs/notes-intro.md")]
mod notes {
    #[doc = include_str!("../docs/notes-ipp.md")]
    mod inner_product_proof {}
    #[doc = include_str!("../docs/notes-rp.md")]
    mod range_proof {}
    #[doc = include_str!("../docs/notes-r1cs.md")]
    mod r1cs_proof {}
}

mod errors;
mod generators;
mod inner_product_proof;
mod linear_proof;
mod r1cs_file;
mod range_proof;
mod transcript;

pub use crate::errors::ProofError;
pub use crate::generators::{BulletproofGens, BulletproofGensShare, PedersenGens};
pub use crate::linear_proof::LinearProof;
pub use crate::r1cs_file::parser;
pub use crate::range_proof::RangeProof;
#[doc = include_str!("../docs/aggregation-api.md")]
pub mod range_proof_mpc {
    pub use crate::errors::MPCError;
    pub use crate::range_proof::dealer;
    pub use crate::range_proof::messages;
    pub use crate::range_proof::party;
}

#[cfg(feature = "std")]
#[cfg(feature = "multiprover")]
pub mod r1cs;

#[cfg(feature = "multiprover")]
#[allow(missing_docs)]
pub mod r1cs_mpc;
