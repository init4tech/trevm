use crate::{
    Block, BlockContext, EvmBlockComplete, EvmErrored, EvmNeedsTx, NeedsBlock, Shanghai, Trevm,
};
use alloy_eips::eip4895::Withdrawal;
use revm::{primitives::SpecId, Database, DatabaseCommit};

/// Driver for a single trevm block. This trait allows a type to specify the
/// entire lifecycle of a trevm block, from opening the block to driving the
/// trevm to completion.
pub trait BlockDriver {
    type Block: Block;

    /// Get a reference to the block filler for this driver.
    fn block(&self) -> &Self::Block;

    /// Prepare the trevm for the block by creating a new block context and
    /// opening the block.
    ///
    /// # Note:
    ///
    /// This function is sealed, and exists only for convenience.
    fn prep_trevm<'a, Ext, Db: Database + DatabaseCommit, TrevmState: NeedsBlock>(
        &self,
        trevm: Trevm<'a, Ext, Db, TrevmState>,
    ) -> Result<EvmNeedsTx<'a, Ext, Db, C>, EvmErrored<'a, Ext, Db, C>> {
        trevm.open_block(self.block(), self.context())
    }

    /// Drive the trevm for the block. This function should be called after
    /// [`BlockDriver::prep_trevm`] and will drive the trevm to completion.
    fn drive_trevm<Ext, Db: Database + DatabaseCommit>(
        &mut self,
        trevm: EvmNeedsTx<'_, Ext, Db, C>,
    ) -> Result<EvmBlockComplete<'_, Ext, Db, C>, EvmErrored<'_, Ext, Db, C>>;
}

pub struct AlloyBlock {
    header: alloy_consensus::Header,
    transactions: Vec<alloy_consensus::TxEnvelope>,
    withdrawals: Vec<Withdrawal>,
}

impl BlockDriver<Shanghai<'_>> for AlloyBlock {
    type Block = alloy_consensus::Header;

    fn block(&self) -> &Self::Block {
        &self.header
    }

    fn drive_trevm<Ext, Db: Database + DatabaseCommit>(
        &mut self,
        trevm: EvmNeedsTx<'_, Ext, Db, Shanghai<'_>>,
    ) -> Result<EvmBlockComplete<'_, Ext, Db, Shanghai<'_>>, EvmErrored<'_, Ext, Db, Shanghai<'_>>>
    {
        todo!()
    }
}
