use crate::Block;
use revm::{
    primitives::{EVMError, ResultAndState},
    Database, DatabaseCommit, Evm,
};

/// Block contexts apply pre-block and post-block logic to the EVM, as well as
/// post-tx logic like receipt generation.
///
/// This trait encapsulates special pre-block and post-block logic that needs to
/// be applied to the EVM. This is useful for implementing EIPs that require
/// special system actions to be taken before and after the block is processed.
///
/// ### Mutability and the EVM
///
/// The [`BlockContext`] trait has mutable access to the EVM, allowing it to
/// modify the EVM state as needed. This is useful for implementing EIPs that
/// require special system actions to be taken before and after the block is
/// processed.
///
/// Because the EVM is passed as a mutable reference, the [`BlockContext`] trait
/// can make ANY modificatiopn to the EVM state. This includes potentially
/// changing the [`BlockEnv`] and [`CfgEnv`] objects, the [`SpecId`], or any
/// other property. As such, block contexts are allowed to violate [`Trevm`]
/// state guarantees. Please be careful.
///
/// ### Provided contexts
///
/// Contexts are provided for [Shanghai], [Cancun], and [Prague]. While most
/// Contexts do not modify previous behavior, older context modify things like
/// the block reward in place. The [Prague] lifecycle is a superset of the
/// [Cancun] lifecycle, and the [Cancun] lifecycle is a superset of the
/// [Shanghai] lifecycle. This means that the [Prague] lifecycle includes all
/// the logic of the [Cancun] and [Shanghai] Contexts.
///
/// [Shanghai]: crate::Shanghai
/// [Cancun]: crate::Cancun
/// [Prague]: crate::Prague
/// [`BlockEnv`]: revm::primitives::BlockEnv
/// [`CfgEnv`]: revm::primitives::CfgEnv
/// [`SpecId`]: revm::primitives::SpecId
/// [`Trevm`]: crate::Trevm
pub trait BlockContext<Ext, Db: Database + DatabaseCommit> {
    /// The error type for the context. This captures logic errors that occur
    /// during the lifecycle.
    type Error: From<EVMError<Db::Error>>;

    /// Apply pre-block logic, and prep the EVM for the first user transaction.
    fn open_block<B: Block>(
        &mut self,
        evm: &mut Evm<'_, Ext, Db>,
        b: &B,
    ) -> Result<(), Self::Error>;

    /// Apply post-transaction logic and then commit the transaction to the evm
    /// state. This will be called by [`Trevm`] for each transaction in a block.
    ///
    /// This is the hook to produce receipts, update cumulative gas used,
    /// inspect logs, etc etc.
    ///
    /// Generally this should end by calling `evm.db_mut().commit(result.state)`
    /// however, it is allowed to discard the transaction instead of committing
    /// it.
    ///
    /// ```
    /// # use revm::{
    /// #     primitives::{EVMError, ResultAndState},
    /// #     Database, DatabaseCommit, Evm,
    /// # };
    /// # use trevm::BlockContext;
    /// # struct MyContext;
    /// #
    /// # impl MyContext { fn make_receipt(&self, result: &ResultAndState) {} }
    /// #
    /// impl<Ext, Db> BlockContext<Ext, Db> for MyContext
    /// where
    ///     Db: Database + DatabaseCommit
    /// {
    /// #    type Error = EVMError<Db::Error>;
    /// #    fn open_block<B: trevm::Block>(
    /// #       &mut self,
    /// #       _evm: &mut Evm<'_, Ext, Db>,
    /// #       _b: &B
    /// #    ) -> Result<(), Self::Error> { Ok(()) }
    ///     fn apply_tx(
    ///        &mut self,
    ///        evm: &mut Evm<'_, Ext, Db>,
    ///        result: ResultAndState
    ///     ) {
    ///         // Do something with the result
    ///         self.make_receipt(&result);
    ///         evm.db_mut().commit(result.state);
    ///     }
    /// #
    /// #    fn close_block(
    /// #       &mut self,
    /// #       _evm: &mut Evm<'_, Ext, Db>
    /// #     ) -> Result<(), Self::Error> {
    /// #       Ok(())
    /// #     }
    /// }
    /// ```
    ///
    /// [`Trevm`]: crate::Trevm
    fn apply_tx(&mut self, trevm: &mut Evm<'_, Ext, Db>, result: ResultAndState);

    /// Apply post-block logic and close the block.
    fn close_block(&mut self, trevm: &mut Evm<'_, Ext, Db>) -> Result<(), Self::Error>;
}
