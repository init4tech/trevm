use crate::{Block, BlockContext, EvmBlockComplete, EvmBlockDriverErrored, EvmNeedsTx};
use revm::{primitives::EVMError, Database, DatabaseCommit};

/// The result of running transactions for a block driver.
pub type RunTxResult<'a, 'b, Ext, Db, C, T> =
    Result<EvmNeedsTx<'a, Ext, Db, C>, EvmBlockDriverErrored<'a, 'b, Ext, Db, C, T>>;

/// The result of driving a block to completion.
pub type DriveBlockResult<'a, 'b, Ext, Db, C, T> =
    Result<EvmBlockComplete<'a, Ext, Db, C>, EvmBlockDriverErrored<'a, 'b, Ext, Db, C, T>>;

/// Driver for a single trevm block. This trait allows a type to specify the
/// entire lifecycle of a trevm block, from opening the block to driving the
/// trevm to completion.
pub trait BlockDriver<'b, Ext, C: BlockContext<Ext>>
where
    Self: 'b,
{
    /// The [`Block`] filler for this driver.
    type Block: Block;

    /// An error type for this driver.
    type Error<Db: Database>: std::error::Error
        + From<EVMError<Db::Error>>
        + From<<C as BlockContext<Ext>>::Error<Db>>;

    /// Get a reference to the block filler for this driver.
    fn block(&self) -> &Self::Block;

    /// Get the context for this block.
    fn context(&'b self) -> C;

    /// Run the transactions for the block.
    fn run_txns<'a, Db: Database + DatabaseCommit>(
        &self,
        trevm: EvmNeedsTx<'a, Ext, Db, C>,
    ) -> RunTxResult<'a, 'b, Ext, Db, C, Self>;

    /// Run post
    fn post_block_checks<Db: Database + DatabaseCommit>(
        &self,
        trevm: &EvmBlockComplete<'_, Ext, Db, C>,
    ) -> Result<(), Self::Error<Db>>;
}
