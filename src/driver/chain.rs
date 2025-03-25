use crate::{helpers::TrevmCtxCommit, BlockDriver, EvmChainDriverErrored, EvmNeedsBlock};
use revm::{context::result::EVMError, primitives::hardfork::SpecId, Database, DatabaseCommit};

/// The result of driving a chain to completion.
pub type DriveChainResult<Ctx, Insp, Inst, Prec, D> =
    Result<EvmNeedsBlock<Ctx, Insp, Inst, Prec>, EvmChainDriverErrored<Ctx, Insp, Inst, Prec, D>>;

/// Driver for a chain of blocks.
pub trait ChainDriver<Insp> {
    /// The block driver for this chain.
    type BlockDriver: BlockDriver<Insp>;

    /// An error type for this driver.
    type Error<Db: Database + DatabaseCommit>: core::error::Error
        + From<EVMError<Db::Error>>
        + From<<Self::BlockDriver as BlockDriver<Insp>>::Error<Db>>;

    /// Get the spec id for a block.
    fn spec_id_for(&self, block: &<Self::BlockDriver as BlockDriver<Insp>>::Block) -> SpecId;

    /// Get the blocks in this chain. The blocks should be in order, and this
    /// function MUST NOT return an empty slice.
    fn blocks(&mut self) -> &mut [Self::BlockDriver];

    /// Checks that run between blocks, e.g. 1559 base fee calculation,
    /// or parent-child relationships.
    ///
    /// The `idx` parameter is the index of the block in the chain.
    fn interblock<Ctx, Inst, Prec>(
        &mut self,
        trevm: &EvmNeedsBlock<Ctx, Insp, Inst, Prec>,
        idx: usize,
    ) -> Result<(), Self::Error<Ctx::Db>>
    where
        Ctx: TrevmCtxCommit;
}
