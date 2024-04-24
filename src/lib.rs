//! A pure-Rust library of thoroughly-tested, serializable CRDT's.
//!
//! [Conflict-free Replicated Data Types][crdt] (CRDTs) are data structures
//! which can be replicated across multiple networked nodes, and whose
//! properties allow for deterministic, local resolution of
//! possible inconsistencies which might result from concurrent
//! operations.
//!
//! [crdt]: https://en.wikipedia.org/wiki/Conflict-free_replicated_data_type
#![crate_type = "lib"]
#![deny(missing_docs)]
#![deny(unreachable_pub)]

mod traits;
pub use crate::traits::{Actor, CmRDT, CvRDT, ResetRemove};

/// This module contains a Last-Write-Wins Register.
pub mod lwwreg;

/// This module contains a Multi-Value Register.
pub mod mvreg;

/// This module contains a Merkle-Dag Register.
#[cfg(feature = "merkle")]
pub mod merkle_reg;

/// This module contains the Vector Clock
pub mod vclock;

/// This module contains the Dot (Actor + Sequence Number)
pub mod dot;

/// This module contains a Max Register.
#[cfg(feature = "num")]
pub mod maxreg;

/// This module contains a Min Register
pub mod minreg;

/// This module contains a dense Identifier.
#[cfg(feature = "num")]
pub mod identifier;

/// This module contains an Observed-Remove Set With Out Tombstones.
pub mod orswot;

/// This module contains a Grow-only Counter.
#[cfg(feature = "num")]
pub mod gcounter;

/// This module contains a Grow-only Set.
pub mod gset;

/// This module contains a Grow-only List.
#[cfg(feature = "num")]
pub mod glist;

/// This module contains a Positive-Negative Counter.
#[cfg(feature = "num")]
pub mod pncounter;

/// This module contains a Map with Reset-Remove and Observed-Remove semantics.
pub mod map;

/// This module contains context for editing a CRDT.
pub mod ctx;

/// This module contains a Sequence.
#[cfg(feature = "num")]
pub mod list;

mod serde_helper;

#[cfg(feature = "num")]
pub use {
    gcounter::GCounter, glist::GList, identifier::Identifier, list::List, maxreg::MaxReg,
    minreg::MinReg, pncounter::PNCounter,
};

// /// Version Vector with Exceptions
// pub mod vvwe;

/// Top-level re-exports for CRDT structures.
pub use crate::{
    dot::Dot, dot::DotRange, dot::OrdDot, gset::GSet, lwwreg::LWWReg, map::Map, mvreg::MVReg,
    orswot::Orswot, vclock::VClock,
};

/// A re-export of the quickcheck crate for external property tests
#[cfg(feature = "quickcheck")]
pub use quickcheck;
