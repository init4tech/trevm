use crate::{driver::RunTxResult, Block, BlockDriver, EvmNeedsTx, Shanghai};
use alloy_consensus::TxEnvelope;
use alloy_primitives::U256;
use revm::{
    primitives::{BlobExcessGasAndPrice, BlockEnv, EVMError},
    Database, DatabaseCommit,
};

impl<'a> From<&'a alloy_rpc_types_eth::Block<TxEnvelope>> for Shanghai<'a> {
    fn from(block: &'a alloy_rpc_types_eth::Block<TxEnvelope>) -> Self {
        block.withdrawals.as_ref().map(|s| Shanghai::new(s)).unwrap_or_default()
    }
}

impl Block for alloy_rpc_types_eth::Header {
    fn fill_block_env(&self, block_env: &mut revm::primitives::BlockEnv) {
        let BlockEnv {
            number,
            coinbase,
            timestamp,
            gas_limit,
            basefee,
            difficulty,
            prevrandao,
            blob_excess_gas_and_price,
        } = block_env;
        *number = U256::from(self.number.unwrap_or_default());
        *coinbase = self.miner;
        *timestamp = U256::from(self.timestamp);
        *gas_limit = U256::from(self.gas_limit);
        *basefee = U256::from(self.base_fee_per_gas.unwrap_or_default());
        *difficulty = U256::from(self.difficulty);
        *prevrandao = self.mix_hash;
        *blob_excess_gas_and_price =
            self.blob_gas_used.map(|ebg| BlobExcessGasAndPrice::new(ebg as u64));
    }
}

/// Error during Ethereum consensus checks.
#[derive(thiserror::Error)]
pub enum AlloyBlockError<Db: Database> {
    /// An error occurred in the EVM.
    #[error("EVM error")]
    EvmError(revm::primitives::EVMError<Db::Error>),

    /// Block contained only tx hashes, without transactions
    #[error("Block contained only tx hashes, without transactions")]
    MissingTransactions,
}

impl<Db: Database> std::fmt::Debug for AlloyBlockError<Db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EvmError(_) => f.debug_struct("EvmError").finish_non_exhaustive(),
            Self::MissingTransactions => f.write_str("MissingTransactions"),
        }
    }
}

impl<Db: Database> From<EVMError<Db::Error>> for AlloyBlockError<Db> {
    fn from(e: EVMError<Db::Error>) -> Self {
        Self::EvmError(e)
    }
}

impl<'b, Ext> BlockDriver<'b, Ext, Shanghai<'b>> for alloy_rpc_types_eth::Block<TxEnvelope> {
    type Block = alloy_rpc_types_eth::Header;

    type Error<Db: Database> = AlloyBlockError<Db>;

    fn block(&self) -> &Self::Block {
        &self.header
    }

    fn context(&'b self) -> Shanghai<'b> {
        self.withdrawals.as_ref().map(|w| Shanghai::new(w.as_slice())).unwrap_or_default()
    }

    fn run_txns<'a, Db: Database + DatabaseCommit>(
        &self,
        mut trevm: EvmNeedsTx<'a, Ext, Db, Shanghai<'b>>,
    ) -> RunTxResult<'a, 'b, Ext, Db, Shanghai<'b>, Self> {
        if !self.transactions.is_full() {
            return Err(trevm.errored(AlloyBlockError::MissingTransactions));
        }

        for transaction in self.transactions.txns() {
            trevm = trevm.run_tx(transaction).map_err(|e| e.err_into())?.accept();
        }
        Ok(trevm)
    }

    fn post_block_checks<Db: Database + DatabaseCommit>(
        &self,
        _trevm: &crate::EvmBlockComplete<'_, Ext, Db, Shanghai<'b>>,
    ) -> Result<(), Self::Error<Db>> {
        // TODO
        Ok(())
    }
}
