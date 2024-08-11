use crate::{Block, BundleDriver, DriveBundleResult};
use alloy_consensus::{Transaction, TxEip4844Variant, TxEnvelope};
use alloy_eips::{eip2718::Decodable2718, BlockNumberOrTag};
use alloy_primitives::{bytes::Buf, keccak256, Address, TxKind, U256};
use alloy_rpc_types_mev::{
    EthCallBundle, EthCallBundleResponse, EthCallBundleTransactionResult, EthSendBundle,
};
use revm::primitives::{EVMError, ExecutionResult};
use thiserror::Error;

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
    /// The bundle has no transactions
    #[error("bundle has no transactions")]
    BundleEmpty,
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
            Self::BundleEmpty => write!(f, "BundleEmpty"),
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
        // Check if the block we're in is valid for this bundle. Both must match
        if trevm.inner().block().number.to::<u64>() != self.bundle.block_number {
            return Err(trevm.errored(BundleError::BlockNumberMismatch));
        }

        // Check if the bundle has any transactions
        if self.bundle.txs.is_empty() {
            return Err(trevm.errored(BundleError::BundleEmpty));
        }

        // Check if the state block number is valid (not 0, and not a tag)
        if !self.bundle.state_block_number.is_number()
            || self.bundle.state_block_number.as_number().unwrap_or(0) == 0
        {
            return Err(trevm.errored(BundleError::BlockNumberMismatch));
        }

        // Set the state block number this simulation was based on
        self.response.state_block_number = self
            .bundle
            .state_block_number
            .as_number()
            .unwrap_or(trevm.inner().block().number.to::<u64>());

        let bundle_filler = BundleBlockFiller::from(&self.bundle);

        let run_result = trevm.try_with_block(&bundle_filler, |trevm| {
            // We need to keep track of the state of the EVM as we run the transactions, so we can accumulate the results.
            // Therefore we keep this mutable trevm instance, and set it to the new one after we're done simulating.
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

            // Cache the pre simulation coinbase balance, so we can use it to calculate the coinbase diff after every tx simulated.
            let initial_coinbase_balance =
                match trevm.try_read_balance(trevm.inner().block().coinbase) {
                    Ok(balance) => balance,
                    Err(e) => {
                        return Err(trevm.errored(BundleError::EVMError {
                            inner: revm::primitives::EVMError::Database(e),
                        }))
                    }
                };
            let mut pre_sim_coinbase_balance = initial_coinbase_balance;
            let post_sim_coinbase_balance = pre_sim_coinbase_balance;
            let mut total_gas_fees = U256::ZERO;
            let mut total_gas_used = 0;

            let mut hash_bytes = Vec::with_capacity(32 * txs.len());

            for tx in txs.iter() {
                let run_result = trevm.run_tx(tx);

                match run_result {
                    // return immediately if errored
                    Err(e) => {
                        return Err(e.map_err(|e| BundleError::EVMError { inner: e }));
                    }
                    // Accept + accumulate state
                    Ok(res) => {
                        let (execution_result, mut committed_trevm) = res.accept();

                        let coinbase = committed_trevm.inner().block().coinbase;
                        let basefee = committed_trevm.inner().block().basefee;
                        let gas_used = execution_result.gas_used();

                        // Fetch the address and coinbase balance after the transaction, to start calculating and results
                        let from_address = tx
                            .recover_signer()
                            .map_err(|e| BundleError::TransactionSenderRecoveryError(e));
                        let from_address = match from_address {
                            Ok(addr) => addr,
                            Err(e) => return Err(committed_trevm.errored(e)),
                        };

                        // Extend the hash bytes with the transaction hash to calculate the bundle hash later
                        hash_bytes.extend_from_slice(tx.tx_hash().as_slice());

                        // Get the post simulation coinbase balance
                        let post_sim_coinbase_balance =
                            match committed_trevm.try_read_balance(coinbase) {
                                Ok(balance) => balance,
                                Err(e) => {
                                    return Err(committed_trevm.errored(BundleError::EVMError {
                                        inner: revm::primitives::EVMError::Database(e),
                                    }))
                                }
                            };

                        // Calculate the gas fees paid
                        let gas_fees = match tx {
                            TxEnvelope::Legacy(tx) => {
                                U256::from(tx.tx().gas_price) * U256::from(gas_used)
                            }
                            TxEnvelope::Eip2930(tx) => {
                                U256::from(tx.tx().gas_price) * U256::from(gas_used)
                            }
                            TxEnvelope::Eip1559(tx) => {
                                U256::from(tx.tx().effective_gas_price(Some(basefee.to::<u64>())))
                                    * U256::from(gas_used)
                            }
                            TxEnvelope::Eip4844(tx) => match tx.tx() {
                                TxEip4844Variant::TxEip4844(tx) => {
                                    U256::from(tx.effective_gas_price(Some(basefee.to::<u64>())))
                                        * U256::from(gas_used)
                                }
                                TxEip4844Variant::TxEip4844WithSidecar(tx) => {
                                    U256::from(tx.tx.effective_gas_price(Some(basefee.to::<u64>())))
                                        * U256::from(gas_used)
                                }
                            },
                            _ => {
                                return Err(committed_trevm
                                    .errored(BundleError::UnsupportedTransactionType))
                            }
                        };

                        // Calculate the gas price
                        let gas_price = match tx {
                            TxEnvelope::Legacy(tx) => U256::from(tx.tx().gas_price),
                            TxEnvelope::Eip2930(tx) => U256::from(tx.tx().gas_price),
                            TxEnvelope::Eip1559(tx) => {
                                U256::from(tx.tx().effective_gas_price(Some(basefee.to::<u64>())))
                            }
                            TxEnvelope::Eip4844(tx) => match tx.tx() {
                                TxEip4844Variant::TxEip4844(tx) => {
                                    U256::from(tx.effective_gas_price(Some(basefee.to::<u64>())))
                                }
                                TxEip4844Variant::TxEip4844WithSidecar(tx) => {
                                    U256::from(tx.tx.effective_gas_price(Some(basefee.to::<u64>())))
                                }
                            },
                            _ => {
                                return Err(committed_trevm
                                    .errored(BundleError::UnsupportedTransactionType))
                            }
                        };

                        let coinbase_diff =
                            post_sim_coinbase_balance.saturating_sub(pre_sim_coinbase_balance);
                        let eth_sent_to_coinbase = coinbase_diff.saturating_sub(gas_fees);

                        total_gas_used += execution_result.gas_used();
                        total_gas_fees += gas_fees;

                        // update the coinbase balance
                        pre_sim_coinbase_balance = post_sim_coinbase_balance;

                        // set the return data for the response
                        let (value, revert) = if execution_result.is_success() {
                            let value = execution_result.into_output().unwrap_or_default();
                            (Some(value), None)
                        } else {
                            let revert = execution_result.into_output().unwrap_or_default();
                            (None, Some(revert))
                        };

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
                            value,
                            revert,
                            gas_used,
                            gas_price,
                            gas_fees,
                        });
                        trevm = committed_trevm;
                    }
                }
            }
            // Accumulate the total results
            self.response.total_gas_used = total_gas_used;
            self.response.coinbase_diff =
                post_sim_coinbase_balance.saturating_sub(initial_coinbase_balance);
            self.response.eth_sent_to_coinbase =
                self.response.coinbase_diff.saturating_sub(total_gas_fees);
            self.response.bundle_gas_price = self
                .response
                .coinbase_diff
                .checked_div(U256::from(total_gas_used))
                .unwrap_or_default();
            self.response.gas_fees = total_gas_fees;
            self.response.bundle_hash = keccak256(hash_bytes);

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
