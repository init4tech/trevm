use crate::{Block, BundleDriver, DriveBundleResult};
use alloy_consensus::TxEnvelope;
use alloy_eips::{eip2718::Decodable2718, BlockNumberOrTag};
use alloy_primitives::U256;
use alloy_rpc_types_mev::{EthCallBundle, EthSendBundle};
use revm::primitives::{EVMError, ExecutionResult};
use thiserror::Error;

/// Possible errors that can occur while driving a bundle.
#[derive(Clone, Error)]
pub enum BundleError<Db: revm::Database> {
    /// The block number of the bundle does not match the block number of the revm block configuration.
    #[error("revm block number must match the bundle block number")]
    BlockNumberMismatch,
    /// The timestamp of the bundle is out of range.
    #[error("timestamp out of range")]
    TimestampOutOfRange,
    /// The bundle was reverted (or halted).
    #[error("bundle reverted")]
    BundleReverted,
    /// An error occurred while decoding a transaction contained in the bundle.
    #[error("transaction decoding error")]
    TransactionDecodingError(#[from] alloy_eips::eip2718::Eip2718Error),
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
            Self::TimestampOutOfRange => write!(f, "TimestampOutOfRange"),
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

        let run_result = trevm.try_with_block(&bundle_filler, |trevm| {
            let mut trevm = trevm;

            for raw_tx in self.txs.clone().into_iter() {
                let tx = TxEnvelope::decode_2718(&mut raw_tx.to_vec().as_slice());

                let tx = match tx {
                    Ok(tx) => tx,
                    Err(e) => return Err(trevm.errored(BundleError::TransactionDecodingError(e))),
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
        });

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

impl<Ext> BundleDriver<Ext> for EthSendBundle {
    type Error<Db: revm::Database> = BundleError<Db>;

    fn run_bundle<'a, Db: revm::Database + revm::DatabaseCommit>(
        &mut self,
        trevm: crate::EvmNeedsTx<'a, Ext, Db>,
    ) -> DriveBundleResult<'a, Ext, Db, Self> {
        // 1. Check if the block we're in is valid for this bundle. Both must match
        if trevm.inner().block().number.to::<u64>() != self.block_number {
            return Err(trevm.errored(BundleError::BlockNumberMismatch));
        }

        // 2. Check for start timestamp range validity
        if let Some(min_timestamp) = self.min_timestamp {
            if trevm.inner().block().timestamp.to::<u64>() < min_timestamp {
                return Err(trevm.errored(BundleError::TimestampOutOfRange));
            }
        }

        // 3. Check for end timestamp range validity
        if let Some(max_timestamp) = self.max_timestamp {
            if trevm.inner().block().timestamp.to::<u64>() > max_timestamp {
                return Err(trevm.errored(BundleError::TimestampOutOfRange));
            }
        }

        let mut t = trevm;

        for raw_tx in self.txs.clone().into_iter() {
            // Decode the transaction
            let tx = TxEnvelope::decode_2718(&mut raw_tx.to_vec().as_slice());

            let tx = match tx {
                Ok(tx) => tx,
                Err(e) => return Err(t.errored(BundleError::TransactionDecodingError(e))),
            };

            // Run the transaction
            let run_result = match t.run_tx(&tx) {
                Ok(res) => res,
                Err(e) => return Err(e.map_err(|e| BundleError::EVMError { inner: e })),
            };

            // Accept the state if the transaction was successful and the bundle did not revert or halt
            let trevm = match run_result.result() {
                ExecutionResult::Success { .. } => run_result.accept_state(),
                ExecutionResult::Revert { .. } | ExecutionResult::Halt { .. } => {
                    // If the transaction reverted but it is contained in the set of transactions allowed to revert,
                    // then we discard the state and move on.
                    if self.reverting_tx_hashes.contains(tx.tx_hash()) {
                        run_result.reject()
                    } else {
                        return Err(run_result.errored(BundleError::BundleReverted));
                    }
                }
            };

            t = trevm;
        }

        Ok(t)
    }

    fn post_bundle<Db: revm::Database + revm::DatabaseCommit>(
        &mut self,
        _trevm: &crate::EvmNeedsTx<'_, Ext, Db>,
    ) -> Result<(), Self::Error<Db>> {
        Ok(())
    }
}
