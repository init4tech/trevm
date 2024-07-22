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
//! Here is the simples possible example:
//!
//! ```
//! use revm::{EvmBuilder, db::InMemoryDB};
//! use trevm::{TrevmBuilder, TransactedError, Cfg, Block, Tx, };
//!
//! # fn t<C: Cfg, B: Block, T: Tx>(cfg: &C, block: &B, tx: &T)
//! # -> Result<(), Box<dyn std::error::Error>> {
//! EvmBuilder::default()
//!     .with_db(InMemoryDB::default())
//!     .build_trevm()
//!     .fill_cfg(cfg)
//!     .fill_block(block)
//!     .apply_tx(tx)
//!     .map_err(TransactedError::into_error)?
//!     .clear_block();
//! # Ok(())
//! # }
//!
//! ```
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
//! Here's a slightly more complex example, with states written out:
//!
//! ```
//! # use revm::{EvmBuilder, db::{InMemoryDB, BundleState}, State,
//! # StateBuilder};
//! # use trevm::{TrevmBuilder, TransactedError, Cfg, Block, Tx, BlockOutput,
//! # EvmNeedsCfg, EvmNeedsFirstBlock, EvmNeedsTx, EvmReady, EvmNeedsNextBlock};
//! # fn t<C: Cfg, B: Block, T: Tx>(cfg: &C, block: &B, tx: &T)
//! # -> Result<(), Box<dyn std::error::Error>> {
//! let state = StateBuilder::new_with_database(InMemoryDB::default()).build();
//!
//! // Trevm starts in `EvmNeedsCfg`.
//! let trevm: EvmNeedsCfg<'_, _, _> = EvmBuilder::default()
//!     .with_db(state)
//!     .build_trevm();
//!
//! // Once the cfg is filled, we move to `EvmNeedsFirstBlock`.
//! let trevm: EvmNeedsFirstBlock<'_, _, _> = trevm.fill_cfg(cfg);
//!
//! // Filling the block gets us to `EvmNeedsTx`.
//! let trevm: EvmNeedsTx<'_, _, _> = trevm.fill_block(block);
//! // Filling the tx gets us to `EvmReady`.
//! let trevm: EvmReady<'_, _, _> = trevm.fill_tx(tx);
//!
//! // Applying the tx or ignoring the error gets us back to `EvmNeedsTx``.
//! let trevm: EvmNeedsTx<'_, _, _> = match trevm.execute_tx() {
//!     Ok(transacted) => transacted.apply(),
//!     Err(e) => e.discard_error(),
//! };
//!
//! // Clearing or closing a block gets us to `EvmNeedsNextBlock`, ready for the
//! // next block.
//! let trevm: EvmNeedsNextBlock<'_, _, _> = trevm.clear_block();
//!
//! // Finishing the EVM gets us the final changes and a list of block outputs
//! // that includes the transaction receipts.
//! let (bundle, outputs): (BundleState, Vec<BlockOutput>) = trevm.finish();
//! # Ok(())
//! # }
//! ```
//!
//! ### Lifecycles
//!
//! Trevm handles pre- and post-block logic through the [`Lifecycle`] trait.
//! The lifecycle trait can be invoked by [`Trevm::open_block`] and
//! [`Trevm::close_block`]. Trevm provides a few lifecycle implementations:
//!
//! - [`ShanghaiLifecycle`]: Shanghai lifecycle applies the post-block system
//!   action (withdrawals) introduced by [EIP-4895].
//! - [`CancunLifecycle`]: Cancun lifecycle applies the [`ShanghaiLifecycle`]
//!   as well as the post-block logic introduced by [EIP-4788].
//! - [`PragueLifecycle`]: Prague lifecycle applies [`ShanghaiLifecycle`] and
//!   [`CancunLifecycle`] as well as the pre-block logic of [EIP-2935] and the
//!   post-block logic introduced by [EIP-7002] and [EIP-7251].
//!
//! Lifecycles before Shanghai are not currently implemented. In particular,
//! block and ommer rewards for pre-merge blocks are not implemented.
//!
//! The [`Lifecycle`] trait methods take a mutable reference to allow the
//! lifecycle to accumulate information about the execution. This is useful for
//! pre-block logic, where the lifecycle may need to accumulate information
//! about the block before the first transaction is executed, and re-use that
//! information to close the block. It may also be used to compute statistics
//! or indices that are only available after the block is closed.
//!
//! Here's the above example using a lifecycle. Note that
//!
//! ```
//! # use revm::{EvmBuilder, db::InMemoryDB};
//! # use trevm::{TrevmBuilder, TransactedError, Cfg, Block, Tx,
//! # ShanghaiLifecycle, CancunLifecycle};
//! # use alloy_primitives::B256;
//! # fn t<C: Cfg, B: Block, T: Tx>(cfg: &C, block: &B, tx: &T)
//! # -> Result<(), Box<dyn std::error::Error>> {
//! // Lifecycles are mutable and can be reused across multiple blocks.
//! let mut lifecycle = CancunLifecycle::<'static> {
//!    parent_beacon_root: B256::repeat_byte(0x42),
//!    shanghai: ShanghaiLifecycle::default(),
//! };
//!
//! EvmBuilder::default()
//!     .with_db(InMemoryDB::default())
//!     .build_trevm()
//!     .fill_cfg(cfg)
//!     // The pre-block logic is applied here
//!     .open_block(block, &mut lifecycle)
//!     // Note that the logic is fallible, so we have to handle errors
//!     .map_err(TransactedError::into_error)?
//!     .apply_tx(tx)
//!     .map_err(TransactedError::into_error)?
//!     // Closing the block applies the post-block logic, and is also fallible
//!     .close_block(&mut lifecycle)
//!     .map_err(TransactedError::into_error)?;
//! # Ok(())
//! # }
//! ```
//!
//! ### Handling execution errors
//!
//! Trevm uses the [`TransactedError`] type to handle errors during transaction
//! execution. This type is a wrapper around the error that occurred, and
//! provides a method to discard the error and continue execution. This is
//! useful when you want to continue executing transactions even if one fails.
//!
//! Usually, errors will be [`EVMError<Db>`], but [`Lifecycle`] implementations
//! may return other errors. The [`TransactedError`] type is generic over the
//! error type, so you can use it with any error type.
//!
//! ```
//! # use revm::{EvmBuilder, db::InMemoryDB};
//! # use trevm::{TrevmBuilder, TransactedError, Cfg, Block, Tx,
//! # ShanghaiLifecycle, CancunLifecycle};
//! # use alloy_primitives::B256;
//! # fn t<C: Cfg, B: Block, T: Tx>(cfg: &C, block: &B, tx: &T)
//! # -> Result<(), Box<dyn std::error::Error>> {
//! // Lifecycles are mutable and can be reused across multiple blocks.
//! let mut lifecycle = CancunLifecycle::<'static> {
//!    parent_beacon_root: B256::repeat_byte(0x42),
//!    shanghai: ShanghaiLifecycle::default(),
//! };
//!
//! match EvmBuilder::default()
//!     .with_db(InMemoryDB::default())
//!     .build_trevm()
//!     .fill_cfg(cfg)
//!     // The pre-block logic is applied here
//!     .open_block(block, &mut lifecycle) {
//!     Ok(trevm) => {
//!         trevm
//!     }
//!     Err(transacted_error) => {
//!         let (trevm, error) = transacted_error.into_parts();
//!         // Handle the error here, and return the EVM if you want
//!         // to keep going
//!         trevm
//!     }
//! };
//! # Ok(())
//! # }
//! ```
//!
//! ### Extending Trevm
//!
//! Trevm has a few extension points:
//!
//! - Build the [`revm::Evm`] with a [`revm::Inspector`] and use it in trevm.
//! - Implement the [`PostTx`] trait to apply post-transaction logic/changes.
//! - Implement your own [`Cfg`], [`Block`], and
//!   [`Tx`] to fill the EVM from your own data structures.
//! - Implement your own [`Lifecycle`] to apply pre- and post-block logic.
//!
//! ```
//! # use trevm::Tx;
//! # use alloy_primitives::Address;
//! // You can implement your own Tx to fill the EVM environment with your own
//! // data.
//! pub struct MyTx;
//!
//! impl Tx for MyTx {
//!    fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
//!       // fill the tx_env with your data
//!       // we recommend destructuring here to safeguard against future changes
//!       // to the TxEnv struct
//!       let revm::primitives::TxEnv {
//!           caller,
//!           ..
//!       } = tx_env;
//!       *caller = Address::repeat_byte(0xde);
//!    }
//! }
//! ```
//!
//! ### Trevm feature flags
//!
//! Trevm passes through most feature flags from revm, the following are on by
//! default:
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
//! [`EVMError<Db>`]: revm::primitives::EVMError<Db>
//! [typestate pattern]: https://cliffle.com/blog/rust-typestate/
//! [crate readme]: https://github.com/init4tt/trevm
//! [EIP-2537]: https://eips.ethereum.org/EIPS/eip-2537
//! [EIP-4844]: https://eips.ethereum.org/EIPS/eip-4844
//! [EIP-4895]: https://eips.ethereum.org/EIPS/eip-4895
//! [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
//! [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251

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
pub use lifecycle::{BlockOutput, CancunLifecycle, Lifecycle, PragueLifecycle, ShanghaiLifecycle};

mod postflight;
pub use postflight::{PostTx, PostflightResult};

mod states;
pub(crate) use states::sealed::*;
pub use states::{EvmNeedsCfg, EvmNeedsFirstBlock, EvmNeedsNextBlock, EvmNeedsTx, EvmReady};

pub mod syscall;

/// Utilities for testing Trevm or testing with Trevm.
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
