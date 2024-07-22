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

    /// Apply the transaction to the evm state
    fn apply_tx(&mut self, trevm: &mut Evm<'_, Ext, Db>, result: ResultAndState);

    /// Apply post-block logic and close the block.
    fn close_block(&mut self, trevm: &mut Evm<'_, Ext, Db>) -> Result<(), Self::Error>;
}
