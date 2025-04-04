use crate::{helpers::Ctx, Block, EvmBlockDriverErrored, EvmNeedsBlock, EvmNeedsTx};
use revm::{
    context::result::EVMError, inspector::NoOpInspector, Database, DatabaseCommit, Inspector,
};

/// The result of running transactions for a block driver.
pub type RunTxResult<T, Db, Insp> =
    Result<EvmNeedsTx<Db, Insp>, EvmBlockDriverErrored<T, Db, Insp>>;

/// The result of driving a block to completion.
pub type DriveBlockResult<T, Db, Insp> =
    Result<EvmNeedsBlock<Db, Insp>, EvmBlockDriverErrored<T, Db, Insp>>;

/// Driver for a single trevm block. This trait allows a type to specify the
/// entire lifecycle of a trevm block, from opening the block to driving the
/// trevm to completion.
pub trait BlockDriver<Db, Insp = NoOpInspector>
where
    Db: Database + DatabaseCommit,
    Insp: Inspector<Ctx<Db>>,
{
    /// The [`Block`] filler for this driver.
    type Block: Block;

    /// An error type for this driver.
    type Error: core::error::Error + From<EVMError<Db::Error>>;

    /// Get a reference to the block filler for this driver.
    fn block(&self) -> &Self::Block;

    /// Run the transactions for the block.
    fn run_txns(&mut self, trevm: EvmNeedsTx<Db, Insp>) -> RunTxResult<Self, Db, Insp>;
    /// Run post
    fn post_block(&mut self, trevm: &EvmNeedsBlock<Db, Insp>) -> Result<(), Self::Error>;
}
