use crate::{BlockDriver, EvmChainDriverErrored, EvmNeedsBlock};
use revm::{
    primitives::{EVMError, SpecId},
    Database, DatabaseCommit,
};

/// The result of driving a chain to completion.
pub type DriveChainResult<'a, Ext, Db, D> =
    Result<EvmNeedsBlock<'a, Ext, Db>, EvmChainDriverErrored<'a, Ext, Db, D>>;

/// Driver for a chain of blocks.
pub trait ChainDriver<Ext> {
    /// The block driver for this chain.
    type BlockDriver: BlockDriver<Ext>;

    /// An error type for this driver.
    type Error<Db: Database + DatabaseCommit>: core::error::Error
        + From<EVMError<Db::Error>>
        + From<<Self::BlockDriver as BlockDriver<Ext>>::Error<Db>>;

    /// Get the spec id for a block.
    fn spec_id_for(&self, block: &<Self::BlockDriver as BlockDriver<Ext>>::Block) -> SpecId;

    /// Get the blocks in this chain. The blocks should be in order, and this
    /// function MUST NOT return an empty slice.
    fn blocks(&mut self) -> &mut [Self::BlockDriver];

    /// Checks that run between blocks, e.g. 1559 base fee calculation,
    /// or parent-child relationships.
    ///
    /// The `idx` parameter is the index of the block in the chain.
    fn interblock<Db: Database + DatabaseCommit>(
        &mut self,
        trevm: &EvmNeedsBlock<'_, Ext, Db>,
        idx: usize,
    ) -> Result<(), Self::Error<Db>>;
}
