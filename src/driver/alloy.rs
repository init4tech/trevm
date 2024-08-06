use crate::{Block, BundleDriver, DriveBundleResult};
use alloy_consensus::TxEnvelope;
use alloy_eips::BlockNumberOrTag;
use alloy_primitives::U256;
use alloy_rlp::Decodable;
use alloy_rpc_types_mev::EthCallBundle;
use revm::primitives::{EVMError, ExecutionResult};
use thiserror::Error;

/// Possible errors that can occur while driving a bundle.
#[derive(Clone, Error)]
pub enum BundleError<Db: revm::Database> {
    /// The block number of the bundle does not match the block number of the revm block configuration.
    #[error("revm block number must match the bundle block number")]
    BlockNumberMismatch,
    /// The bundle was reverted (or halted).
    #[error("bundle reverted")]
    BundleReverted,
    /// An error occurred while decoding a transaction contained in the bundle.
    #[error("transaction decoding error")]
    TransactionDecodingError(#[from] alloy_rlp::Error),
    /// An error occurred while running the EVM.
    #[error("internal EVM Error")]
    EVMError {
        /// The error that occurred while running the EVM.
        inner: EVMError<Db::Error>,
    },
}

impl<Db: revm::Database> From<EVMError<Db::Error>> for BundleError<Db> {
    fn from(inner: EVMError<Db::Error>) -> Self {
        Self::EVMError { inner }
    }
}

impl<Db: revm::Database> std::fmt::Debug for BundleError<Db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BlockNumberMismatch => write!(f, "BlockNumberMismatch"),
            Self::BundleReverted => write!(f, "BundleReverted"),
            Self::TransactionDecodingError(e) => write!(f, "TransactionDecodingError({:?})", e),
            Self::EVMError { .. } => write!(f, "EVMError"),
        }
    }
}

/// A block filler for the bundle, used to fill in the block data specified for the bundle.
#[derive(Clone, Debug)]
struct BundleBlockFiller {
    pub block_number: BlockNumberOrTag,
    pub timestamp: Option<u64>,
    pub gas_limit: Option<u64>,
    pub difficulty: Option<U256>,
    pub base_fee: Option<u128>,
}

impl Block for BundleBlockFiller {
    fn fill_block_env(&self, block_env: &mut revm::primitives::BlockEnv) {
        if let Some(timestamp) = self.timestamp {
            block_env.timestamp = U256::from(timestamp);
        }
        if let Some(gas_limit) = self.gas_limit {
            block_env.gas_limit = U256::from(gas_limit);
        }
        if let Some(difficulty) = self.difficulty {
            block_env.difficulty = difficulty;
        }
        if let Some(base_fee) = self.base_fee {
            block_env.basefee = U256::from(base_fee);
        }
        if let Some(block_number) = self.block_number.as_number() {
            block_env.number = U256::from(block_number);
        }
    }
}

impl From<EthCallBundle> for BundleBlockFiller {
    fn from(bundle: EthCallBundle) -> Self {
        Self {
            block_number: bundle.state_block_number,
            timestamp: bundle.timestamp,
            gas_limit: bundle.gas_limit,
            difficulty: bundle.difficulty,
            base_fee: bundle.base_fee,
        }
    }
}

impl<Ext> BundleDriver<Ext> for EthCallBundle {
    type Error<Db: revm::Database> = BundleError<Db>;

    fn run_bundle<'a, Db: revm::Database + revm::DatabaseCommit>(
        &mut self,
        trevm: crate::EvmNeedsTx<'a, Ext, Db>,
    ) -> DriveBundleResult<'a, Ext, Db, Self> {
        // 1. Check if the block we're in is valid for this bundle. Both must match
        if trevm.inner().block().number.to::<u64>() != self.block_number {
            return Err(trevm.errored(BundleError::BlockNumberMismatch));
        }

        let bundle_filler = BundleBlockFiller::from(self.clone());

        let run_result = trevm.try_with_block(
            |trevm| {
                let mut trevm = trevm;

                for raw_tx in self.txs.clone().into_iter() {
                    let tx = TxEnvelope::decode(&mut raw_tx.to_vec().as_slice());

                    let tx = match tx {
                        Ok(tx) => tx,
                        Err(e) => {
                            return Err(trevm.errored(BundleError::TransactionDecodingError(e)))
                        }
                    };

                    let run_result = trevm.run_tx(&tx);

                    match run_result {
                        // return immediately if errored
                        Err(e) => {
                            return Err(e.map_err(|e| BundleError::EVMError { inner: e }));
                        }
                        // Accept the state, and move on
                        Ok(res) => match res.result() {
                            ExecutionResult::Revert { .. } | ExecutionResult::Halt { .. } => {
                                return Err(res.errored(BundleError::BundleReverted));
                            }
                            ExecutionResult::Success { .. } => {
                                trevm = res.accept_state();
                            }
                        },
                    }
                }

                // return the final state
                Ok(trevm)
            },
            &bundle_filler,
        );

        match run_result {
            Ok(trevm) => Ok(trevm),
            Err(e) => Err(e),
        }
    }

    fn post_bundle<Db: revm::Database + revm::DatabaseCommit>(
        &mut self,
        _trevm: &crate::EvmNeedsTx<'_, Ext, Db>,
    ) -> Result<(), Self::Error<Db>> {
        Ok(())
    }
}
