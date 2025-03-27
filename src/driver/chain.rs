use crate::{helpers::Ctx, BlockDriver, EvmChainDriverErrored, EvmNeedsBlock};
use revm::{
    context::result::EVMError, primitives::hardfork::SpecId, Database, DatabaseCommit, Inspector,
};

/// The result of driving a chain to completion.
pub type DriveChainResult<Db, Insp, D> =
    Result<EvmNeedsBlock<Db, Insp>, EvmChainDriverErrored<Db, Insp, D>>;

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
    fn interblock<Db>(
        &mut self,
        trevm: &EvmNeedsBlock<Db, Insp>,
        idx: usize,
    ) -> Result<(), Self::Error<Db>>
    where
        Db: Database + DatabaseCommit,
        Insp: Inspector<Ctx<Db>>;
}
