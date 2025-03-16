//! [`Trevm`] - a typestate interface to [`revm`].
//!
//! Trevm provides a safe and low-overhead way to interact with the EVM. It is
//! based on the [typestate pattern], which allows the compiler to enforce
//! correct usage of the EVM.
//!
//! Trevm is NOT an EVM implementation. It is a thin wrapper around the EVM
//! provided by [`revm`].
//!
//! [`Trevm`] models the EVM as a state machine with the following states:
//!
//! - [`EvmNeedsCfg`]: The EVM needs to be configured.
//! - [`EvmNeedsBlock`]: The EVM is configured and needs a block environment.
//! - [`EvmNeedsTx`]: The EVM is configured and has a block environment, and
//!   now needs a transaction to execute.
//! - [`EvmReady`]: The EVM has a transaction loaded and is ready to execute it.
//! - [`EvmErrored`]: The EVM has executed a transaction and encountered an
//!   error.
//! - [`EvmTransacted`]: The EVM has executed a transaction successfully.
//!
//! ## Quickstart
//!
//! To get started, use a [`revm::EvmBuilder`] to configure the EVM, then call
//! [`TrevmBuilder::build_trevm`] to construct the [`Trevm`] instance. From
//! there, you should do the following:
//!
//! - Fill a Cfg by calling [`Trevm::fill_cfg`] with a [`Cfg`].
//! - Open a block by calling [`Trevm::fill_block`] with a [`Block`].
//! - Fill a Tx by calling [`Trevm::fill_tx`] with a [`Tx`].
//! - Run the transaction by calling [`Trevm::run_tx`].
//! - Handle the result by calling [`EvmTransacted::accept`] or
//!   [`EvmTransacted::reject`].
//! - Call [`Trevm::close_block`] to close the block.
//! - Then call [`Trevm::finish`] to get the outputs.
//!
//!
//! ### Running a transaction
//!
//! Running transactions is simple with Trevm. Here's a basic example:
//!
//! ```
//! use revm::{EvmBuilder, db::InMemoryDB};
//! use trevm::{TrevmBuilder, EvmErrored, Cfg, Block, Tx};
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
//! macro generates type aliases for the Trevm states with concrete `Ext` and `Db` types.
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
//! ### [`BlockDriver`] and [`ChainDriver`]
//!
//! Trevm handles transaction application, receipts, and pre- and post-block
//! logic through the [`BlockDriver`] and [`ChainDriver`] traits. These
//! traits invoked by [`Trevm`] via [`EvmNeedsBlock::drive_block`] and
//! [`EvmNeedsCfg::drive_chain`], respectively.
//!
//! To aid in the creation of drivers, Trevm offers helper functions for
//! common eips:
//!
//! - [`eip2935`] - Prague's [EIP-2935], which updates historical block
//!   hashes in a special system contract.
//! - [`eip4788`] - Cancun's [EIP-4788], which updates historical beacon
//!   roots in a special system contract.
//! - [`eip4895`] - Cancun's [EIP-4895], which processes withdrawal
//!   requests by crediting accounts.
//! - [`eip6110`] - Prague's [EIP-6110], which extracts deposit
//!   requests from the withdrawal contract events.
//! - [`eip7002`] - Prague's [EIP-7002], which extracts withdrawal requests
//!   from the system withdrawal contract state.
//! - [`eip7251`] - Prague's [EIP-7251], which extracts
//!   consolidation requests from the system consolidation contract state.
//!
//! The [`BlockDriver`] and [`ChainDriver`] trait methods take a mutable
//! reference to allow the driver to accumulate information about the
//! execution. This is useful for accumulating receipts, senders, or other
//! information that is more readily available during execution. It is also
//! useful for pre-block logic, where the lifecycle may need to accumulate
//! information about the block before the first transaction is executed, and
//! re-use that information to close the block. It may also be used to compute
//! statistics or indices that are only available after the block is closed.
//!
//! ```
//! # use revm::{EvmBuilder, db::InMemoryDB};
//! # use trevm::{TrevmBuilder, EvmErrored, Cfg, BlockDriver};
//! # use alloy::primitives::B256;
//! # fn t<C: Cfg, D: BlockDriver<()>>(cfg: &C, mut driver: D)
//! # -> Result<(), Box<dyn std::error::Error>> {
//! let trevm = EvmBuilder::default()
//!     .with_db(InMemoryDB::default())
//!     .build_trevm()
//!     .fill_cfg(cfg)
//!     .drive_block(&mut driver);
//! # Ok(())
//! # }
//! ```
//!
//! [`BlockDriver`] and [`ChainDriver`] implementations are generic over the
//! `Ext` type. This means that you can use customized revm extensions and
//! inspectors in your driver logic.
//!
//! ### Handling execution errors
//!
//! Trevm uses the [`EvmErrored`] state to handle errors during transaction
//! execution. This type is a wrapper around the error that occurred, and
//! provides a method to discard the error and continue execution. This is
//! useful when you want to continue executing transactions even if one fails.
//!
//! Usually, errors will be [`EVMError<Db>`], but [`BlockDriver`] and
//! [`ChainDriver`] implementations may return other errors. The [`EvmErrored`]
//! type is generic over the error type, so you can use it with any error type.
//!
//! ```
//! # use revm::{EvmBuilder, db::InMemoryDB};
//! # use trevm::{TrevmBuilder, EvmErrored, Cfg, Block, Tx};
//! # use alloy::primitives::B256;
//! # fn t<C: Cfg, B: Block, T: Tx>(cfg: &C, block: &B, tx: &T)
//! # -> Result<(), Box<dyn std::error::Error>> {
//! let trevm = match EvmBuilder::default()
//!     .with_db(InMemoryDB::default())
//!     .build_trevm()
//!     .fill_cfg(cfg)
//!     .fill_block(block)
//!     .fill_tx(tx)
//!     .run() {
//!         Ok(trevm) => trevm.accept_state(),
//!         Err(e) => e.discard_error(),
//!     };
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
//! - Implement your own [`BlockDriver`] to apply pre- and post-block logic,
//!   use custom receipt types, or more.
//!
//! ```
//! # use trevm::Tx;
//! # use alloy::primitives::Address;
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
//! ## Understanding the state machine
//!
//! Here's an example, with states written out:
//!
//! ```
//! # use revm::{EvmBuilder, db::{InMemoryDB, BundleState}, State,
//! # StateBuilder};
//! # use trevm::{TrevmBuilder, EvmErrored, Cfg, Block, Tx, BlockOutput,
//! # EvmNeedsCfg, EvmNeedsBlock, EvmNeedsTx, EvmReady, EvmTransacted};
//! # fn t<C: Cfg, B: Block, T: Tx>(cfg: &C, block: &B, tx: &T)
//! # -> Result<(), Box<dyn std::error::Error>> {
//! let state = StateBuilder::new_with_database(InMemoryDB::default()).build();
//!
//! // Trevm starts in `EvmNeedsCfg`.
//! let trevm: EvmNeedsCfg<'_, _, _> = EvmBuilder::default()
//!     .with_db(state)
//!     .build_trevm();
//!
//! // Once the cfg is filled, we move to `EvmNeedsBlock`.
//! let trevm: EvmNeedsBlock<'_, _, _> = trevm.fill_cfg(cfg);
//!
//! // Filling the block gets us to `EvmNeedsTx`.
//! let trevm: EvmNeedsTx<'_, _, _> = trevm.fill_block(
//!     block,
//! );
//! // Filling the tx gets us to `EvmReady`.
//! let trevm: EvmReady<'_, _, _> = trevm.fill_tx(tx);
//!
//! let res: Result<
//!     EvmTransacted<'_, _, _>,
//!     EvmErrored<'_, _, _, _>,
//! > = trevm.run();
//!
//!
//! // Applying the tx or ignoring the error gets us back to `EvmNeedsTx`.
//! // You could also make additional checks and discard the success result here
//! let trevm: EvmNeedsTx<'_, _, _> = match res {
//!    Ok(trevm) => trevm.accept_state(),
//!    Err(e) => e.discard_error(),
//! };
//!
//! // Clearing or closing a block gets us to `EvmNeedsBlock`, ready for the
//! // next block.
//! let trevm: EvmNeedsBlock<'_, _, _> = trevm
//!     .close_block();
//!
//! // Finishing the EVM gets us the final changes and a list of block outputs
//! // that includes the transaction receipts.
//! let bundle: BundleState = trevm.finish();
//! # Ok(())
//! # }
//! ```
//!
//! ## Happy Path Loop
//!
//! The most simple, straightforward application of Trevm is applying a
//! set of transaction to the EVM. This is done by following :
//!
//! ```none
//! +-----+      +-----------+
//! |Start| ---> |EvmNeedsCfg|
//! +-----+      +-----------+
//!                   |
//!                   +-- fill_cfg() --+
//!                                    |
//!                                    V
//! +------+             +-------------+
//! |Finish|<- finish() -|EvmNeedsBlock|---+
//! +------+             +-------------+   |
//!                        ^               |
//!                        |               |
//!            +-----------+               |
//!            |                           |
//!       close_block()                    |
//!            |                           |
//!   +----------+                         |
//!   |EvmNeedsTx| <---- fill_block() -----+
//!   +----------+
//!    ^       |                           +--------+
//!    |       +------- fill_tx() -------> |EvmReady|--+
//!    |                                   +--------+  |
//!    |             +-------------+                   |
//!    +- accept() --|EvmTransacted| <-- run_tx() -----+
//!    or reject()   +-------------+
//! ```
//!
//! A basic block loop should look like this:
//!
//! ```no_compile
//! let mut evm = evm
//!     .fill_cfg(cfg);
//!     .fill_block(block, pre_block_logic);
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
//! [crate readme]: https://github.com/init4tech/trevm
//! [EIP-2537]: https://eips.ethereum.org/EIPS/eip-2537
//! [EIP-2935]: https://eips.ethereum.org/EIPS/eip-2935
//! [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
//! [EIP-4844]: https://eips.ethereum.org/EIPS/eip-4844
//! [EIP-4895]: https://eips.ethereum.org/EIPS/eip-4895
//! [EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110
//! [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
//! [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
//! [`eip2935`]: crate::system::eip2935
//! [`eip4788`]: crate::system::eip4788
//! [`eip4895`]: crate::system::eip4895
//! [`eip6110`]: crate::system::eip6110
//! [`eip7002`]: crate::system::eip7002
//! [`eip7251`]: crate::system::eip7251

#![doc(
    html_logo_url = "https://raw.githubusercontent.com/alloy-rs/core/main/assets/alloy.jpg",
    html_favicon_url = "https://raw.githubusercontent.com/alloy-rs/core/main/assets/favicon.ico"
)]
#![cfg_attr(not(test), warn(unused_crate_dependencies))]
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]
#![deny(unused_must_use, rust_2018_idioms)]
#![warn(missing_docs, missing_copy_implementations, missing_debug_implementations)]

#[macro_use]
mod macros;

mod connect;
pub use connect::{DbConnect, EvmFactory};

/// Contains database implementations and related
pub mod db;

mod driver;
pub use driver::{
    BlockDriver, BundleDriver, BundleError, BundleProcessor, ChainDriver, DriveBlockResult,
    DriveBundleResult, DriveChainResult, RunTxResult,
};

mod evm;
pub use evm::Trevm;

#[cfg(feature = "estimate_gas")]
mod est;
#[cfg(feature = "estimate_gas")]
pub use est::EstimationResult;

mod ext;
pub use ext::EvmExtUnchecked;

mod fill;
pub use fill::{fillers, Block, Cfg, NoopBlock, NoopCfg, Tx};

pub mod journal;

mod lifecycle;
pub use lifecycle::{ethereum_receipt, BlockOutput, PostTx, PostflightResult};

mod states;
pub(crate) use states::sealed::*;
pub use states::{
    EvmBlockDriverErrored, EvmBundleDriverErrored, EvmChainDriverErrored, EvmErrored,
    EvmNeedsBlock, EvmNeedsCfg, EvmNeedsTx, EvmReady, EvmTransacted,
};

pub mod system;

pub use revm;

/// Utilities for testing Trevm or testing with Trevm.
#[cfg(any(test, feature = "test-utils"))]
pub mod test_utils;

use revm::{Database, EvmBuilder};

/// The minimum gas required for a transaction.
pub const MIN_TRANSACTION_GAS: u64 = 21_000;

/// Ext trait for [`EvmBuilder`] that builds a [`Trevm`], and adds features for
/// [`DbConnect`].
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
