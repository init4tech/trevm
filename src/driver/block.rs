use crate::{helpers::TrevmCtxCommit, Block, EvmBlockDriverErrored, EvmNeedsBlock, EvmNeedsTx};
use revm::{context::result::EVMError, Database, DatabaseCommit};

/// The result of running transactions for a block driver.
pub type RunTxResult<Ctx, Insp, Inst, Prec, T> =
    Result<EvmNeedsTx<Ctx, Insp, Inst, Prec>, EvmBlockDriverErrored<Ctx, Insp, Inst, Prec, T>>;

/// The result of driving a block to completion.
pub type DriveBlockResult<Ctx, Insp, Inst, Prec, T> =
    Result<EvmNeedsBlock<Ctx, Insp, Inst, Prec>, EvmBlockDriverErrored<Ctx, Insp, Inst, Prec, T>>;

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
    fn run_txns<'a, Ctx, Inst, Prec>(
        &mut self,
        trevm: EvmNeedsTx<Ctx, Insp, Inst, Prec>,
    ) -> RunTxResult<Ctx, Insp, Inst, Prec, Self>
    where
        Ctx: TrevmCtxCommit;

    /// Run post
    fn post_block<Ctx, Inst, Prec>(
        &mut self,
        trevm: &EvmNeedsBlock<Ctx, Insp, Inst, Prec>,
    ) -> Result<(), Self::Error<Ctx::Db>>
    where
        Ctx: TrevmCtxCommit;
}
