use crate::{Block, EvmBlockDriverErrored, EvmNeedsBlock, EvmNeedsTx};
use revm::{primitives::EVMError, Database, DatabaseCommit};

/// The result of running transactions for a block driver.
pub type RunTxResult<'a, Ext, Db, T> =
    Result<EvmNeedsTx<'a, Ext, Db>, EvmBlockDriverErrored<'a, Ext, Db, T>>;

/// The result of driving a block to completion.
pub type DriveBlockResult<'a, Ext, Db, T> =
    Result<EvmNeedsBlock<'a, Ext, Db>, EvmBlockDriverErrored<'a, Ext, Db, T>>;

/// Driver for a single trevm block. This trait allows a type to specify the
/// entire lifecycle of a trevm block, from opening the block to driving the
/// trevm to completion.
pub trait BlockDriver<Ext> {
    /// The [`Block`] filler for this driver.
    type Block: Block;

    /// An error type for this driver.
    type Error<Db: Database + DatabaseCommit>: core::error::Error + From<EVMError<Db::Error>>;

    /// Get a reference to the block filler for this driver.
    fn block(&self) -> &Self::Block;

    /// Run the transactions for the block.
    fn run_txns<'a, Db: Database + DatabaseCommit>(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> RunTxResult<'a, Ext, Db, Self>;

    /// Run post
    fn post_block<Db: Database + DatabaseCommit>(
        &mut self,
        trevm: &EvmNeedsBlock<'_, Ext, Db>,
    ) -> Result<(), Self::Error<Db>>;
}
