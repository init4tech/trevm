use crate::{BlockContext, BlockDriver, EvmBlockComplete, EvmChainDriverErrored, EvmNeedsBlock};
use revm::{
    primitives::{EVMError, SpecId},
    Database, DatabaseCommit,
};

/// The result of driving a chain to completion.
pub type DriveChainResult<'a, 'b, Ext, Db, C, D> =
    Result<(Vec<C>, EvmNeedsBlock<'a, Ext, Db>), EvmChainDriverErrored<'a, 'b, Ext, Db, C, D>>;

/// Driver for a chain of blocks.
pub trait ChainDriver<'b, C: BlockContext> {
    /// The block driver for this chain.
    type BlockDriver: BlockDriver<'b, C>;

    /// An error type for this driver.
    type Error<Db: Database>: std::error::Error
        + From<EVMError<Db::Error>>
        + From<<C as BlockContext>::Error<Db>>
        + From<<Self::BlockDriver as BlockDriver<'b, C>>::Error<Db>>;

    /// Get the spec id for a block.
    fn spec_id_for(&self, block: &<Self::BlockDriver as BlockDriver<'b, C>>::Block) -> SpecId;

    /// Get the blocks in this chain. The blocks should be in order, and this
    /// function MUST NOT return an empty slice.
    fn blocks(&self) -> &[Self::BlockDriver];

    /// Checks that run between blocks, e.g. 1559 base fee calculation,
    /// or parent-child relationships.
    ///
    /// The `idx` parameter is the index of the block in the chain.
    fn check_interblock<Ext, Db: Database + DatabaseCommit>(
        &self,
        trevm: &EvmBlockComplete<'_, Ext, Db, C>,
        idx: usize,
    ) -> Result<(), Self::Error<Db>>;
}
