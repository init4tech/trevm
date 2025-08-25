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
//! # Usage Example
//!
//! ```
//! # use revm::database::BundleState;
//! # use trevm::journal::{BundleStateIndex, JournalEncode, JournalDecode, JournalDecodeError};
//! # fn make_index(bundle_state: &BundleState) -> Result<(), JournalDecodeError> {
//! // Make an index over a bundle state.
//! let index = BundleStateIndex::from(bundle_state);
//!
//! // We can serialize it and deserialize it :)
//! let serialized_index = index.encoded();
//! let decoded = BundleStateIndex::decode(&mut serialized_index.as_ref())?;
//! assert_eq!(index, decoded);
//!
//! // It contains information about accounts
//! for (addr, diff) in index.state {
//!     println!("Balance of {addr} changed by {}", diff.balance_change());
//! }
//!
//! // And about bytecode
//! let contract_count = index.new_contracts.len();
//! println!("{contract_count} new contracts deployed!");
//! # Ok(())
//! # }
//! ```
//!
//! [`StateBuilder::with_bundle_update`]: revm::database::StateBuilder::with_bundle_update
//! [`State<Db>`]: revm::database::State
//! [`BundleState`]: revm::database::BundleState
//! [reth]: https://github.com/paradigmxyz/reth

mod coder;
pub use coder::{JournalDecode, JournalDecodeError, JournalEncode};

mod index;
pub use index::{AcctDiff, BundleStateIndex, InfoOutcome};

mod update;
pub use update::BlockUpdate;
