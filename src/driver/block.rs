use crate::{helpers::Ctx, Block, EvmBlockDriverErrored, EvmNeedsBlock, EvmNeedsTx};
use revm::{context::result::EVMError, Database, DatabaseCommit, Inspector};

/// The result of running transactions for a block driver.
pub type RunTxResult<Db, Insp, T> =
    Result<EvmNeedsTx<Db, Insp>, EvmBlockDriverErrored<Db, Insp, T>>;

/// The result of driving a block to completion.
pub type DriveBlockResult<Db, Insp, T> =
    Result<EvmNeedsBlock<Db, Insp>, EvmBlockDriverErrored<Db, Insp, T>>;

/// Driver for a single trevm block. This trait allows a type to specify the
/// entire lifecycle of a trevm block, from opening the block to driving the
/// trevm to completion.
pub trait BlockDriver<Insp> {
    /// The [`Block`] filler for this driver.
    type Block: Block;

    /// An error type for this driver.
    type Error<Db: Database + DatabaseCommit>: core::error::Error + From<EVMError<Db::Error>>;

    /// Get a reference to the block filler for this driver.
    fn block(&self) -> &Self::Block;

    /// Run the transactions for the block.
    fn run_txns<Db>(&mut self, trevm: EvmNeedsTx<Db, Insp>) -> RunTxResult<Db, Insp, Self>
    where
        Db: Database + DatabaseCommit,
        Insp: Inspector<Ctx<Db>>;

    /// Run post
    fn post_block<Db>(&mut self, trevm: &EvmNeedsBlock<Db, Insp>) -> Result<(), Self::Error<Db>>
    where
        Db: Database + DatabaseCommit,
        Insp: Inspector<Ctx<Db>>;
}
