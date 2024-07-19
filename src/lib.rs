//! [`Trevm`] - a typestate interface to [`revm`].
//!
//! Tevm provides a safe and low-overhead way to interact with the EVM. It is
//! based on the [typestate pattern], which allows the compiler to enforce
//! correct usage of the EVM.
//!
//! Tevm is NOT an EVM implementation. It is a thin wrapper around the EVM
//! provided by [`revm`], which is a Rust implementation of the Ethereum
//! Virtual Machine.
//!
//! [`Trevm`] models the EVM as a state machine with the following states:
//!
//! - [`EvmNeedsCfg`]: The EVM needs to be configured.
//! - [`EvmNeedsFirstBlock`]: The EVM is configured and needs a block
//!   environment.
//! - [`EvmNeedsTx`]: The EVM is configured and has a block environment, and
//!   now needs a transaction to execute.
//! - [`EvmReady`]: The EVM has a transaction loaded and is ready to execute it.
//! - [`TransactedError`]: The EVM has executed a transaction and encountered an
//!   error.
//! - [`Transacted`]: The EVM has executed a transaction successfully.
//! - [`EvmNeedsNextBlock`]: The EVM has executed a transaction (or several
//!   transactions) successfully and the block has been closed. The EVM is now
//!   ready to open the next block, or to yield its outputs.
//!
//! ## Quickstart
//!
//! To get started, use a [`revm::EvmBuilder`] to configure the EVM, then call
//! [`TrevmBuilder::build_trevm`] to construct the [`Trevm`] instance. From
//! there, you should do the following:
//!
//! - Fill a Cfg by calling [`Trevm::fill_cfg`] with a [`Cfg`].
//! - Open a block by calling [`Trevm::open_block`] with a [`Block`].
//! - Fill a Tx by calling [`Trevm::fill_tx`] with a [`Tx`].
//! - Run the transaction by calling [`Trevm::execute_tx`].
//! - Handle the result by calling [`Transacted::apply`] or
//!   [`Transacted::discard`].
//! - Call [`Trevm::close_block`] to close the block.
//! - Then call [`Trevm::finish`] to get the outputs.
//!
//! When writing your code, we strongly recommend using the aliases:
//!
//! - [`Trevm`] for the EVM typestate machine in no specific state.
//! - [`EvmNeedsCfg`] for the initial state.
//! - [`EvmNeedsFirstBlock`] for the state after configuring the EVM.
//! - [`EvmNeedsTx`] for the state after opening a block.
//! - [`EvmReady`] for the state after filling a transaction.
//! - [`Transacted`] for the state after executing a transaction.
//! - [`EvmNeedsNextBlock`] for the state after closing a block.
//!
//! We also recommend defining concrete types for `Ext` and `Db` whenever
//! possible, to simplify your code and remove bounds. Most users will want
//! `()` for `Ext`, unless specifically using an inspector or a customized EVM.
//!
//! ### Extending Trevm
//!
//! Trevm has a few extension points:
//!
//! - Build the [`revm::Evm`] with a [`revm::Inspector`] and use it in trevm.
//! - Implement the [`PostTx`] trait to apply post-transaction logic/changes.
//! - Implement your own [`Cfg`], [`Block`], and
//!   [`Tx`] to fill the EVM from your own data structures.
//!
//! ### Trevm feature flags
//!
//! Trevm passes through most feature flags from revm:
//!
//! - `c-kzg` - Enable KZG precompiles as specced for [EIP-4844].
//! - `blst` - Enable BLST precompiles as speced for [EIP-2537].
//! - `portable` - Compiles BLST in portable mode.
//! - `secp256k1` - Use libsecp256k1 for ecrecover (default is k256).
//!
//! Cfg features:
//! - `memory_limit` - Allow users to limit callframe memory usage.
//! - `optional_balance_check` - Allow transacting with insufficient balance.
//! - `optional_block_gas_limit` - Allow transactions that exceed the block gas
//!   limit.
//! - `optional_eip3607` - Allow transactions whose sender account has contract
//!   code.
//! - `optional_gas_refund` - Allow disabling gas refunds, as in Avalanche.
//! - `optional_no_base_fee` - Allow disabling basefee checks.
//! - `optional_beneficiary_reward` - Allow disabling fees and rewards paid to
//!   the block beneficiary.
//!
//! - `dev` - Enable all Cfg features.
//!
//! ### Testing using Trevm
//!
//! Trevm provides a `test-utils` module for easy testing. The test-utils gives
//! you access to an in-memory clean-slate [`Trevm`] instance, as well as tools
//! for directly modifying the state of the EVM.
//!
//! During testing you can use
//! - set balance, nonce, codehash for any account
//! - a single-function setup for a blank EVM
//! - pre-funding for any number of accounts
//!
//! ## Happy Path Loop
//!
//! The most simple, straightforward application of Tevm is applying a
//! set of transaction to the EVM. This is done by following :
//!
//! ```none
//! +-----+      +-----------+
//! |Start| ---> |EvmNeedsCfg|
//! +-----+      +-----------+
//!                   |                  +--------------------+
//!                   +-- fill_cfg() --> | EvmNeedsFirstBlock |
//!                                      +--------------------+
//!              +-----------------+                |
//!     +------- |EvmNeedsNextBlock|----------------+
//!     |        +-----------------+                |
//!     |            ^                              |
//!   finish()       |                              |
//!     |       close_block()                       |
//!     V            |                              |
//!  +------+   +----------+                        |
//!  |Finish}   |EvmNeedsTx| <------ open_block() --+
//!  +------+   +----------+
//!              ^       |                                +--------+
//!              |       +------- fill_tx() ------------> |EvmReady|
//!              |                                        +--------+
//!              |             +----------+                   |
//!              +- apply() ---|Transacted| <-- execute_tx() -+
//!              or discard()  +----------+
//! ```
//!
//! A basic block loop should look like this:
//!
//! ```no_compile
//! let mut evm = evm
//!     .fill_cfg(cfg);
//!     .open_block(block, pre_block_logic);
//!
//! for tx in txs {
//!     // apply the transaction, discard the error if any
//!     evm = match evm.apply_tx(tx) {
//!         Ok(evm) => evm,
//!         Err(e) => { e.discard_error() }
//!     }
//! }
//!
//! // close out the EVM, getting the final state
//! let (bundle, outputs) = evm.close_block(block, post_block_logic).finish();
//! ```
//!
//! [typestate pattern]: https://cliffle.com/blog/rust-typestate/
//! [crate readme]: https://github.com/init4tt/trevm
//! [EIP-4844]: https://eips.ethereum.org/EIPS/eip-4844
//! [EIP-2537]: https://eips.ethereum.org/EIPS/eip-2537

#![doc(
    html_logo_url = "https://raw.githubusercontent.com/alloy-rs/core/main/assets/alloy.jpg",
    html_favicon_url = "https://raw.githubusercontent.com/alloy-rs/core/main/assets/favicon.ico"
)]
#![cfg_attr(not(test), warn(unused_crate_dependencies))]
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]

mod alloy;

mod evm;
pub use evm::{Transacted, TransactedError, Trevm};

mod fill;
pub use fill::{Block, Cfg, Tx};

mod lifecycle;
pub use lifecycle::Lifecycle;

mod output;
pub use output::BlockOutput;

mod postflight;
pub use postflight::{PostTx, PostflightResult};

mod states;
pub(crate) use states::sealed::*;
pub use states::{EvmNeedsCfg, EvmNeedsFirstBlock, EvmNeedsNextBlock, EvmNeedsTx, EvmReady};

pub mod syscall;

#[cfg(feature = "test-utils")]
pub mod test_utils;

use revm::{Database, EvmBuilder};

/// Ext trait for [`EvmBuilder`] that builds a [`Trevm`].
pub trait TrevmBuilder<'a, Ext, Db: Database> {
    /// Builds the [`Trevm`].
    fn build_trevm(self) -> EvmNeedsCfg<'a, Ext, Db>;
}

impl<'a, Stage, Ext, Db: Database> TrevmBuilder<'a, Ext, Db> for EvmBuilder<'a, Stage, Ext, Db> {
    /// Builds the [`Trevm`].
    fn build_trevm(self) -> EvmNeedsCfg<'a, Ext, Db> {
        Trevm::from(self.build())
    }
}
