//! Utilities for serializing revm's [`BundleState`] into a canonical format.
//!
//! The [`BundleState`] represents the accumulated state changes of one or more
//! transactions. It is produced when revm is run with a [`State<Db>`] and the
//! [`StateBuilder::with_bundle_update`] option. It is useful for aggregating
//! state changes across multiple transactions, so that those changes may be
//! stored in a DB, or otherwise processed in a batch.
//!
//! This module contains utilities for serializing the [`BundleState`] in a
//! canonical format that can be stored to disk or sent over the wire. The core
//! type is the [`BundleStateIndex`], which is a sorted list of [`AcctDiff`]s
//! along with new contract bytecode.
//!
//! Each [`AcctDiff`] represents the state changes for a single account, and
//! contains the pre- and post-state of the account, along with sorted changes
//! to the account's storage.
//!
//! The coding scheme is captured by the [`JournalEncode`] and [`JournalDecode`]
//! traits. These traits provide a very simple binary encoding. The encoding
//! prioritizes legibility and simplicity over compactness. We assume that it
//! will be compressed before being stored or sent.
//!
//! [`StateBuilder::with_bundle_update`]: revm::db::StateBuilder::with_bundle_update
//! [`State<Db>`]: revm::db::State
//! [`BundleState`]: revm::db::BundleState
//! [reth]: https://github.com/paradigmxyz/reth

mod coder;
pub use coder::{JournalDecode, JournalDecodeError, JournalEncode};

mod index;
pub use index::{AcctDiff, BundleStateIndex, InfoOutcome};
