//! [`Trevm`] - a typestate interface to [`revm`].
//!
//! Tevm provides a safe and low-overhead way to interact with the EVM. It is
//! based on the [typestate pattern], which allows the compiler to enforce
//! correct usage of the EVM.
//!
//! Tevm is NOT an EVM implementation. It is a thin wrapper around the EVM
//! provided by [`revm`].
//!
//! [`Trevm`] models the EVM as a state machine with the following states:
//!
//! - [`EvmNeedsCfg`]: The EVM needs to be configured.
//! - [`EvmNeedsFirstBlock`]: The EVM is configured and needs a block
//!   environment.
//! - [`EvmNeedsTx`]: The EVM is configured and has a block environment, and
//!   now needs a transaction to execute.
//! - [`EvmReady`]: The EVM has a transaction loaded and is ready to execute it.
//! - [`EvmErrored`]: The EVM has executed a transaction and encountered an
//!   error.
//! - [`EvmTransacted`]: The EVM has executed a transaction successfully.
//! - [`EvmBlockComplete`]: The EVM has executed and closed a block and contains
//!   some a populated [`BlockContext`] object
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
//! - Run the transaction by calling [`Trevm::run_tx`].
//! - Handle the result by calling [`EvmTransacted::accept`] or
//!   [`EvmTransacted::reject`].
//! - Call [`Trevm::close_block`] to close the block.
//! - Call[ [`Trevm::take_context`] to get the context object or
//!   [`Trevm::discard_context`] to drop it.
//! - Then call [`Trevm::finish`] to get the outputs.
//!
//!
//! ### Running a transaction
//!
//! Running transactions is simple with Trevm. Here's a basic example:
//!
//! ```
//! use revm::{EvmBuilder, db::InMemoryDB};
//! use trevm::{TrevmBuilder, EvmErrored, Cfg, Block, Tx, };
//!
//! # fn t<C: Cfg, B: Block, T: Tx>(cfg: &C, block: &B, tx: &T)
//! # -> Result<(), Box<dyn std::error::Error>> {
//! EvmBuilder::default()
//!     .with_db(InMemoryDB::default())
//!     .build_trevm()
//!     .fill_cfg(cfg)
//!     .fill_block(block)
//!     .run_tx(tx);
//! # Ok(())
//! # }
//! ```
//! If you get stuck, don't worry! You _cannot_ invoke the wrong function or
//! mess up the inner state unless you access a method marked `_unchecked`.
//! While the states and generics may seem intimidating at first, they fade
//! into the background when you start writing your application.
//!
//! ## Writing an application
//!
//! When writing your code, we strongly recommend using the `Evm____` type
//! aliases to simplify your code.
//!
//! We also recommend defining concrete types for `Ext` and `Db` whenever
//! possible, to simplify your code and remove bounds. Most users will want
//! `()` for `Ext`, unless specifically using an inspector or a customized EVM.
//!
//! To help you use concrete types, we provide the [`trevm_aliases`] macro. This
//! macro generates type aliases for the Trevm states with a concrete `Ext` and
//!
//! ```
//! use trevm::trevm_aliases;
//! use revm::db::InMemoryDB;
//!
//! // produces types that look like this:
//! // type EvmNeedsCfg = trevm::EvmNeedsCfg<'static, (), InMemoryDB>;
//! trevm_aliases!(revm::db::InMemoryDB);
//! ```
//!
//! ## Understanding the state machine
//!
//! Here's a slightly more complex example, with states written out:
//!
//! ```
//! # use revm::{EvmBuilder, db::{InMemoryDB, BundleState}, State,
//! # StateBuilder};
//! # use trevm::{TrevmBuilder, EvmErrored, Cfg, Block, Tx, BlockOutput,
//! # EvmNeedsCfg, EvmNeedsFirstBlock, EvmNeedsTx, EvmReady, EvmNeedsNextBlock,
//! # EvmBlockComplete, Shanghai, EvmTransacted};
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
//! // Filling the block gets us to `EvmNeedsTx`. `open_block` takes a
//! // context object that will apply pre- and post-block logic, accumulate
//! // receipts, and perform other lifecycle tasks.
//! let trevm: EvmNeedsTx<'_, _, _, _> = trevm.open_block(
//!     block,
//!     Shanghai::default()
//! ).map_err(EvmErrored::into_error)?;
//! // Filling the tx gets us to `EvmReady`.
//! let trevm: EvmReady<'_, _, _, _> = trevm.fill_tx(tx);
//!
//! let res: Result<
//!     EvmTransacted<'_, _, _, _>,
//!     EvmErrored<'_, _, _, _>,
//! > = trevm.run();
//!
//!
//! // Applying the tx or ignoring the error gets us back to `EvmNeedsTx`.
//! // You could also make additional checks and discard the success result here
//! let trevm: EvmNeedsTx<'_, _, _, _> = match res {
//!    Ok(trevm) => trevm.accept(),
//!    Err(e) => e.discard_error(),
//! };
//!
//! // Clearing or closing a block gets us to `EvmNeedsNextBlock`, ready for the
//! // next block.
//! let trevm: EvmBlockComplete<'_, _, _, _> = trevm
//!     .close_block()
//!     .map_err(EvmErrored::into_error)?;;
//!
//! // During block execution, a context object
//! let (context, trevm): (Shanghai<'_>, EvmNeedsNextBlock<'_, _, _>) = trevm
//!     .take_context();
//!
//! // Finishing the EVM gets us the final changes and a list of block outputs
//! // that includes the transaction receipts.
//! let bundle: BundleState = trevm.finish();
//! # Ok(())
//! # }
//! ```
//!
//! ### [`BlockContext`]
//!
//! Trevm handles transaction application, receipts, and pre- and post-block
//! logic through the [`BlockContext`] trait. The [`BlockContext`] trait is
//! invoked by [`Trevm`] to manage the lifecycle of a single block. At the start
//! of a block, the context is opened with [`BlockContext::open_block`], and at
//! the end of the block, the context is closed with
//! [`BlockContext::close_block`]. After each transaction, the context's
//! [`BlockContext::after_tx`] logic controls how and whether the execution
//! result is applied to the EVM state, and handles per-transaction logic like
//! generating receipts and tracking senders.
//!
//! Trevm provides a few block context implementations:
//!
//! - [`Shanghai`]: Shanghai context applies the post-block system
//!   action (withdrawals) introduced by [EIP-4895].
//! - [`Cancun`]: Cancun context applies the [`Shanghai`]
//!   as well as the post-block logic introduced by [EIP-4788].
//! - [`Prague`]: Prague context applies [`Shanghai`] and
//!   [`Cancun`] as well as the pre-block logic of [EIP-2935], the
//!   post-block logic introduced by [EIP-7002] and [EIP-7251], and the
//!   withdrawal request accumulation logic introduced in [EIP-6110].
//! - [`BasicContext`]: Basic context applies no pre- or post-block logic, and
//!   is useful for testing or for applications that do not require the
//!   real system state.
//!
//! Contexts before Shanghai are not currently implemented. In particular,
//! block and ommer rewards for pre-merge blocks are not implemented.
//!
//! The [`BlockContext`] trait methods take a mutable reference to allow the
//! context to accumulate information about the execution. This is useful for
//! accumulating receipts, senders, or other information that is more readily
//! available during execution. It is also useful for pre-block logic, where
//! the lifecycle may need to accumulate information about the block before the
//! first transaction is executed, and re-use that information to close the
//! block. It may also be used to compute statistics or indices that are only
//! available after the block is closed.
//!
//! ```
//! # use revm::{EvmBuilder, db::InMemoryDB};
//! # use trevm::{TrevmBuilder, EvmErrored, Cfg, Block, Tx,
//! # Shanghai, Cancun};
//! # use alloy_primitives::B256;
//! # fn t<C: Cfg, B: Block, T: Tx>(cfg: &C, block: &B, tx: &T)
//! # -> Result<(), Box<dyn std::error::Error>> {
//! // Contexts manage the lifecycle of a single block
//! let mut context = Cancun::<'static> {
//!    parent_beacon_root: B256::repeat_byte(0x42),
//!    shanghai: Shanghai::default(),
//! };
//!
//! let (context, trevm) = EvmBuilder::default()
//!     .with_db(InMemoryDB::default())
//!     .build_trevm()
//!     .fill_cfg(cfg)
//!     // The pre-block logic is applied here
//!     .open_block(block, context)
//!     // Note that the logic is fallible, so we have to handle errors
//!     .map_err(EvmErrored::into_error)?
//!     .run_tx(tx)
//!     .map_err(EvmErrored::into_error)?
//!     .accept()
//!     // Closing the block applies the post-block logic, and is also fallible
//!     .close_block()
//!     .map_err(EvmErrored::into_error)?
//!     // This splits the context, and puts trevm into `EvmNeedsNextBlock`
//!     .take_context();
//! # Ok(())
//! # }
//! ```
//!
//! ### Handling execution errors
//!
//! Trevm uses the [`EvmErrored`] state to handle errors during transaction
//! execution. This type is a wrapper around the error that occurred, and
//! provides a method to discard the error and continue execution. This is
//! useful when you want to continue executing transactions even if one fails.
//!
//! Usually, errors will be [`EVMError<Db>`], but [`BlockContext`]
//! implementations may return other errors. The [`EvmErrored`] type is
//! generic over the error type, so you can use it with any error type.
//!
//! ```
//! # use revm::{EvmBuilder, db::InMemoryDB};
//! # use trevm::{TrevmBuilder, EvmErrored, Cfg, Block, Tx,
//! # Shanghai, Cancun};
//! # use alloy_primitives::B256;
//! # fn t<C: Cfg, B: Block, T: Tx>(cfg: &C, block: &B, tx: &T)
//! # -> Result<(), Box<dyn std::error::Error>> {
//! // Contexts manage the lifecycle of a single block
//! let mut context = Cancun::<'static> {
//!    parent_beacon_root: B256::repeat_byte(0x42),
//!    shanghai: Shanghai::default(),
//! };
//!
//! match EvmBuilder::default()
//!     .with_db(InMemoryDB::default())
//!     .build_trevm()
//!     .fill_cfg(cfg)
//!     // The pre-block logic is applied here
//!     .open_block(block, context) {
//!     Ok(trevm) => {
//!         trevm
//!     }
//!     Err(transacted_error) => {
//!         let (trevm, error) = transacted_error.take_error();
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
//! - Implement your own [`BlockContext`] to apply pre- and post-block logic,
//!   use custom receipt types, or more.
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
//! Trevm also provides the following:
//!
//! - `test-utils` - activates revm's `test-utils` feature, and provides
//!   convenience functions for instantiating [`Trevm`] with an in-memory DB.
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
//!                   |                       +--------------------+
//!                   +-- fill_cfg() -------> | EvmNeedsFirstBlock |
//!                                           +--------------------+
//!                                                          |
//!         +----------------+                               |
//!     +-- |EvmBlockComplete|--take_context()-+             |
//!     |   +----------------+  or discard     |             |
//!     |            ^                         V             |
//!     |            |              +-----------------+      |
//!   finish()       |              |EvmNeedsNextBlock|------+
//!     |       close_block()       +-----------------+      |
//!     V            |                                       |
//!  +------+   +----------+                                 |
//!  |Finish|   |EvmNeedsTx| <------ open_block() -----------+
//!  +------+   +----------+
//!              ^       |                           +--------+
//!              |       +------- fill_tx() -------> |EvmReady|--+
//!              |                                   +--------+  |
//!              |             +-------------+                   |
//!              +- accept() --|EvmTransacted| <-- run_tx() -----+
//!              or reject()   +-------------+
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
//!     evm = match evm.run_tx(tx);
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

mod evm;
pub use evm::Trevm;

mod fill;
pub use fill::{Block, Cfg, NoopBlock, NoopCfg, Tx};

mod lifecycle;
pub use lifecycle::{
    BasicContext, BlockContext, BlockOutput, Cancun, PostTx, PostflightResult, Prague, Shanghai,
};

mod states;
pub(crate) use states::sealed::*;
pub use states::{
    EvmBlockComplete, EvmErrored, EvmNeedsCfg, EvmNeedsFirstBlock, EvmNeedsNextBlock, EvmNeedsTx,
    EvmReady, EvmTransacted,
};

pub mod syscall;

pub use revm;

/// Utilities for testing Trevm or testing with Trevm.
#[cfg(feature = "test-utils")]
pub mod test_utils;

use revm::{Database, DatabaseCommit, EvmBuilder};

/// Ext trait for [`EvmBuilder`] that builds a [`Trevm`].
pub trait TrevmBuilder<'a, Ext, Db: Database + DatabaseCommit> {
    /// Builds the [`Trevm`].
    fn build_trevm(self) -> EvmNeedsCfg<'a, Ext, Db>;
}

impl<'a, Stage, Ext, Db: Database + DatabaseCommit> TrevmBuilder<'a, Ext, Db>
    for EvmBuilder<'a, Stage, Ext, Db>
{
    /// Builds the [`Trevm`].
    fn build_trevm(self) -> EvmNeedsCfg<'a, Ext, Db> {
        Trevm::from(self.build())
    }
}
