use std::fmt::Debug;

use crate::{Block, BundleDriver, DriveBundleResult};
use alloy_consensus::TxEnvelope;
use alloy_eips::BlockNumberOrTag;
use alloy_primitives::U256;
use alloy_rlp::Decodable;
use alloy_rpc_types_mev::EthCallBundle;
use revm::primitives::EVMError;
use thiserror::Error;

#[derive(Debug, Clone, Error)]
enum BundleError<Db: revm::Database> {
    #[error("revm block number must match the bundle block number")]
    BlockNumberMimatch,
    #[error("Internal EVM Error")]
    EVMError { inner: EVMError<Db::Error> },
}

impl<Db: revm::Database> From<EVMError<Db::Error>> for BundleError<Db> {
    fn from(inner: EVMError<Db::Error>) -> Self {
        Self::EVMError { inner }
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
        if trevm.inner().block().number.to() != self.block_number {
            return Err(trevm.errored(BundleError::BlockNumberMimatch));
        }

        let bundle_filler = BundleBlockFiller::from(self.clone());

        let trevm = trevm.with_block(
            |trevm| {
                let mut trevm = trevm;

                for raw_tx in self.txs.into_iter() {
                    let tx = TxEnvelope::decode(&mut raw_tx.to_vec().as_slice()).unwrap();
                    let run_result = trevm.run_tx(&tx);

                    match run_result {
                        // return immediately if errored
                        Err(e) => return e,
                        // Accept the state, and move on
                        Ok(res) => {
                            trevm = res.accept_state();
                        }
                    }
                }

                // return the final state
                trevm
            },
            &bundle_filler,
        );

        Ok(trevm)
    }

    fn post_bundle<Db: revm::Database + revm::DatabaseCommit>(
        &mut self,
        _trevm: &crate::EvmNeedsTx<'_, Ext, Db>,
    ) -> Result<(), Self::Error<Db>> {
        Ok(())
    }
}
