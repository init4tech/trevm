use crate::{Block, BundleDriver, DriveBundleResult};
use alloy_consensus::{Transaction, TxEnvelope};
use alloy_eips::{eip2718::Decodable2718, BlockNumberOrTag};
use alloy_primitives::{bytes::Buf, Address, TxKind, U256};
use alloy_rpc_types_mev::{
    EthCallBundle, EthCallBundleResponse, EthCallBundleTransactionResult, EthSendBundle,
};
use revm::primitives::{EVMError, ExecutionResult};
use thiserror::Error;

/// A bundle simulator which can be used to drive a bundle with a [BundleDriver] and accumulate the results of the bundle.
#[derive(Debug)]
pub struct BundleSimulator<B, R> {
    /// The bundle to simulate.
    pub bundle: B,
    /// The response to the bundle simulation.
    pub response: R,
}

impl<B, R> BundleSimulator<B, R> {
    /// Create a new bundle simulator with the given bundle and response.
    pub const fn new(bundle: B, response: R) -> Self {
        Self { bundle, response }
    }
}

impl<Ext> BundleDriver<Ext> for BundleSimulator<EthCallBundle, EthCallBundleResponse> {
    type Error<Db: revm::Database> = BundleError<Db>;

    fn run_bundle<'a, Db: revm::Database + revm::DatabaseCommit>(
        &mut self,
        trevm: crate::EvmNeedsTx<'a, Ext, Db>,
    ) -> DriveBundleResult<'a, Ext, Db, Self> {
        // 1. Check if the block we're in is valid for this bundle. Both must match
        if trevm.inner().block().number.to::<u64>() != self.bundle.block_number {
            return Err(trevm.errored(BundleError::BlockNumberMismatch));
        }

        let bundle_filler = BundleBlockFiller::from(&self.bundle);

        let run_result = trevm.try_with_block(&bundle_filler, |trevm| {
            let mut trevm = trevm;

            let txs = self
                .bundle
                .txs
                .iter()
                .map(|tx| TxEnvelope::decode_2718(&mut tx.chunk()))
                .collect::<Result<Vec<_>, _>>();
            let txs = match txs {
                Ok(txs) => txs,
                Err(e) => return Err(trevm.errored(BundleError::TransactionDecodingError(e))),
            };

            let pre_bundle_coinbase_balance =
                match trevm.try_read_balance(trevm.inner().block().coinbase) {
                    Ok(balance) => balance,
                    Err(e) => {
                        return Err(trevm.errored(BundleError::EVMError {
                            inner: revm::primitives::EVMError::Database(e),
                        }))
                    }
                };

            for tx in txs.iter() {
                let run_result = trevm.run_tx(tx);

                match run_result {
                    // return immediately if errored
                    Err(e) => {
                        return Err(e.map_err(|e| BundleError::EVMError { inner: e }));
                    }
                    // Accept + accumulate state
                    Ok(res) => match res.result() {
                        ExecutionResult::Revert { .. } | ExecutionResult::Halt { .. } => {
                            return Err(res.errored(BundleError::BundleReverted));
                        }
                        ExecutionResult::Success { .. } => {
                            let (execution_result, mut committed_trevm) = res.accept();
                            let coinbase = committed_trevm.inner().block().coinbase;
                            let basefee = committed_trevm.inner().block().basefee;

                            let from_address = tx
                                .recover_signer()
                                .map_err(|e| BundleError::TransactionSenderRecoveryError(e));
                            let from_address = match from_address {
                                Ok(addr) => addr,
                                Err(e) => return Err(committed_trevm.errored(e)),
                            };
                            let post_simulation_coinbase_balance = match committed_trevm
                                .try_read_balance(coinbase)
                            {
                                Ok(balance) => balance,
                                Err(e) => {
                                    return Err(committed_trevm.errored(BundleError::EVMError {
                                        inner: revm::primitives::EVMError::Database(e),
                                    }))
                                }
                            };
                            let eth_sent_to_coinbase = match post_simulation_coinbase_balance
                                .checked_sub(pre_bundle_coinbase_balance)
                            {
                                Some(diff) => diff,
                                None => {
                                    return Err(committed_trevm
                                        .errored(BundleError::CoinbaseBalanceUnderflow))
                                }
                            };
                            let gas_fee_paid = match tx {
                                TxEnvelope::Legacy(tx) => {
                                    U256::from(tx.tx().gas_price)
                                        * U256::from(execution_result.gas_used())
                                }
                                TxEnvelope::Eip2930(tx) => {
                                    U256::from(tx.tx().gas_price)
                                        * U256::from(execution_result.gas_used())
                                }
                                TxEnvelope::Eip1559(tx) => {
                                    (basefee + U256::from(tx.tx().max_priority_fee_per_gas))
                                        * U256::from(execution_result.gas_used())
                                }
                                TxEnvelope::Eip4844(_) => U256::ZERO,
                                _ => {
                                    return Err(committed_trevm
                                        .errored(BundleError::UnsupportedTransactionType))
                                }
                            };
                            let tx_gas_price = match tx {
                                TxEnvelope::Legacy(tx) => U256::from(tx.tx().gas_price),
                                TxEnvelope::Eip2930(tx) => U256::from(tx.tx().gas_price),
                                TxEnvelope::Eip1559(tx) => U256::from(
                                    tx.tx().effective_gas_price(Some(basefee.to::<u64>())),
                                ),
                                TxEnvelope::Eip4844(_) => U256::ZERO,
                                _ => {
                                    return Err(committed_trevm
                                        .errored(BundleError::UnsupportedTransactionType))
                                }
                            };
                            let coinbase_diff = pre_bundle_coinbase_balance + eth_sent_to_coinbase;

                            // Accumulate the total results
                            self.response.eth_sent_to_coinbase += eth_sent_to_coinbase;
                            self.response.coinbase_diff += coinbase_diff;
                            self.response.gas_fees += gas_fee_paid;
                            self.response.total_gas_used += execution_result.gas_used();
                            self.response.bundle_gas_price += tx_gas_price;

                            // Push the result of the bundle's transaction to the response
                            self.response.results.push(EthCallBundleTransactionResult {
                                tx_hash: *tx.tx_hash(),
                                coinbase_diff,
                                eth_sent_to_coinbase,
                                from_address,
                                to_address: match tx.to() {
                                    TxKind::Call(to) => Some(to),
                                    _ => Some(Address::ZERO),
                                },
                                value: execution_result.output().cloned(),
                                revert: None,
                                gas_used: execution_result.gas_used(),
                                gas_price: tx_gas_price,
                                gas_fees: gas_fee_paid,
                            });
                            trevm = committed_trevm;
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

/// Possible errors that can occur while driving a bundle.
#[derive(Error)]
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
    /// An unsupported transaction type was encountered.
    #[error("unsupported transaction type")]
    UnsupportedTransactionType,
    /// The coinbase balance underflowed
    #[error("coinbase balance underflowed")]
    CoinbaseBalanceUnderflow,
    /// An error occurred while decoding a transaction contained in the bundle.
    #[error("transaction decoding error")]
    TransactionDecodingError(#[from] alloy_eips::eip2718::Eip2718Error),
    /// An error ocurred while recovering the sender of a transaction
    #[error("transaction sender recovery error")]
    TransactionSenderRecoveryError(#[from] alloy_primitives::SignatureError),
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
            Self::UnsupportedTransactionType => write!(f, "UnsupportedTransactionType"),
            Self::CoinbaseBalanceUnderflow => write!(f, "CoinbaseBalanceUnderflow"),
            Self::TransactionSenderRecoveryError(e) => {
                write!(f, "TransactionSenderRecoveryError({:?})", e)
            }
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

impl From<&EthCallBundle> for BundleBlockFiller {
    fn from(bundle: &EthCallBundle) -> Self {
        Self {
            block_number: bundle.state_block_number,
            timestamp: bundle.timestamp,
            gas_limit: bundle.gas_limit,
            difficulty: bundle.difficulty,
            base_fee: bundle.base_fee,
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

            let txs = self
                .txs
                .iter()
                .map(|tx| TxEnvelope::decode_2718(&mut tx.chunk()))
                .collect::<Result<Vec<_>, _>>();
            let txs = match txs {
                Ok(txs) => txs,
                Err(e) => return Err(trevm.errored(BundleError::TransactionDecodingError(e))),
            };

            for tx in txs.iter() {
                let run_result = trevm.run_tx(tx);

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

        let txs = self
            .txs
            .iter()
            .map(|tx| TxEnvelope::decode_2718(&mut tx.chunk()))
            .collect::<Result<Vec<_>, _>>();
        let txs = match txs {
            Ok(txs) => txs,
            Err(e) => return Err(trevm.errored(BundleError::TransactionDecodingError(e))),
        };

        let mut t = trevm;

        for tx in txs.iter() {
            // Run the transaction
            let run_result = match t.run_tx(tx) {
                Ok(res) => res,
                Err(e) => return Err(e.map_err(|e| BundleError::EVMError { inner: e })),
            };

            // Accept the state if the transaction was successful and the bundle did not revert or halt
            let trevm = match run_result.result() {
                ExecutionResult::Success { .. } => run_result.accept_state(),
                ExecutionResult::Revert { .. } | ExecutionResult::Halt { .. } => {
                    // If the transaction reverted but it is contained in the set of transactions allowed to revert,
                    // then we _accept_ the state and move on.
                    // See https://github.com/flashbots/rbuilder/blob/52fea312e5d8be1f1405c52d1fd207ecee2d14b1/crates/rbuilder/src/building/order_commit.rs#L546-L558
                    if self.reverting_tx_hashes.contains(tx.tx_hash()) {
                        run_result.accept_state()
                    } else {
                        return Err(run_result.errored(BundleError::BundleReverted));
                    }
                }
            };

            // Make sure to update the trevm instance we're using to simulate with the latest one
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
