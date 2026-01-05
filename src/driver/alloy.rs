use crate::{
    helpers::Ctx,
    system::{
        MAX_BLOB_GAS_PER_BLOCK_CANCUN, MAX_BLOB_GAS_PER_BLOCK_OSAKA, MAX_BLOB_GAS_PER_BLOCK_PRAGUE,
    },
    Block, BundleDriver, DriveBundleResult,
};
use alloy::{
    consensus::{
        crypto::RecoveryError, transaction::SignerRecoverable, Transaction, TxEip4844Variant,
        TxEnvelope,
    },
    eips::{eip2718::Decodable2718, BlockNumberOrTag},
    primitives::{bytes::Buf, keccak256, Address, Bytes, TxKind, U256},
    rpc::types::mev::{
        EthBundleHash, EthCallBundle, EthCallBundleResponse, EthCallBundleTransactionResult,
        EthSendBundle,
    },
};
use revm::{
    context::result::{EVMError, ExecutionResult},
    primitives::hardfork::SpecId,
    Database, DatabaseCommit, Inspector,
};

/// Possible errors that can occur while driving a bundle.
pub enum BundleError<Db: Database> {
    /// The block number of the bundle does not match the block number of the revm block configuration.
    BlockNumberMismatch,
    /// The timestamp of the bundle is out of range.
    TimestampOutOfRange,
    /// The bundle was reverted (or halted).
    BundleReverted,
    /// The bundle has no transactions
    BundleEmpty,
    /// Too many blob transactions
    Eip4844BlobGasExceeded,
    /// An unsupported transaction type was encountered.
    UnsupportedTransactionType,
    /// An error occurred while decoding a transaction contained in the bundle.
    TransactionDecodingError(alloy::eips::eip2718::Eip2718Error),
    /// An error occurred while recovering the sender of a transaction.
    TransactionSenderRecoveryError(alloy::consensus::crypto::RecoveryError),
    /// An error occurred while running the EVM.
    EVMError {
        /// The error that occurred while running the EVM.
        inner: EVMError<Db::Error>,
    },
}

impl<Db: Database> core::fmt::Display for BundleError<Db> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::BlockNumberMismatch => {
                write!(f, "revm block number must match the bundle block number")
            }
            Self::TimestampOutOfRange => write!(f, "timestamp out of range"),
            Self::BundleReverted => write!(f, "bundle reverted"),
            Self::BundleEmpty => write!(f, "bundle has no transactions"),
            Self::Eip4844BlobGasExceeded => write!(f, "max blob gas limit exceeded"),
            Self::UnsupportedTransactionType => write!(f, "unsupported transaction type"),
            Self::TransactionDecodingError(err) => write!(f, "transaction decoding error: {err}"),
            Self::TransactionSenderRecoveryError(err) => {
                write!(f, "transaction sender recovery error: {err}")
            }
            Self::EVMError { inner } => write!(f, "internal EVM error: {inner}"),
        }
    }
}

impl<Db: Database> From<alloy::eips::eip2718::Eip2718Error> for BundleError<Db> {
    fn from(err: alloy::eips::eip2718::Eip2718Error) -> Self {
        Self::TransactionDecodingError(err)
    }
}

impl<Db: Database> From<alloy::primitives::SignatureError> for BundleError<Db> {
    fn from(err: alloy::primitives::SignatureError) -> Self {
        Self::TransactionSenderRecoveryError(err.into())
    }
}

impl<Db: Database> From<EVMError<Db::Error>> for BundleError<Db> {
    fn from(inner: EVMError<Db::Error>) -> Self {
        Self::EVMError { inner }
    }
}

impl<Db: Database> std::error::Error for BundleError<Db> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::TransactionDecodingError(err) => Some(err),
            Self::TransactionSenderRecoveryError(err) => Some(err),
            _ => None,
        }
    }
}

impl<Db: Database> From<RecoveryError> for BundleError<Db> {
    fn from(err: RecoveryError) -> Self {
        Self::TransactionSenderRecoveryError(err)
    }
}

impl<Db: Database> core::fmt::Debug for BundleError<Db> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::TimestampOutOfRange => write!(f, "TimestampOutOfRange"),
            Self::BlockNumberMismatch => write!(f, "BlockNumberMismatch"),
            Self::BundleEmpty => write!(f, "BundleEmpty"),
            Self::BundleReverted => write!(f, "BundleReverted"),
            Self::TransactionDecodingError(e) => write!(f, "TransactionDecodingError({e:?})"),
            Self::UnsupportedTransactionType => write!(f, "UnsupportedTransactionType"),
            Self::Eip4844BlobGasExceeded => write!(f, "Eip4844BlobGasExceeded"),
            Self::TransactionSenderRecoveryError(e) => {
                write!(f, "TransactionSenderRecoveryError({e:?})")
            }
            Self::EVMError { .. } => write!(f, "EVMError"),
        }
    }
}

/// A bundle processor which can be used to drive a bundle with a [BundleDriver], accumulate the results of the bundle and dispatch
/// a response.
#[derive(Debug)]
pub struct BundleProcessor<B, R> {
    /// The bundle to process.
    pub bundle: B,
    /// The response for the processed bundle.
    response: R,
}

impl<B, R> BundleProcessor<B, R>
where
    R: Default,
{
    /// Create a new bundle simulator with the given bundle and response.
    pub fn new(bundle: B) -> Self {
        Self { bundle, response: R::default() }
    }

    /// Clear the driver, resetting the response. This resets the driver,
    /// allowing for resimulation of the same bundle.
    pub fn clear(&mut self) -> R {
        core::mem::take(&mut self.response)
    }
}

impl<B, R> From<B> for BundleProcessor<B, R>
where
    R: Default,
{
    fn from(bundle: B) -> Self {
        Self::new(bundle)
    }
}

impl<B, R> BundleProcessor<B, R> {
    /// Decode and validate the transactions in the bundle, performing EIP4844 gas checks.
    pub fn decode_and_validate_txs<Db: Database + DatabaseCommit>(
        txs: &[Bytes],
    ) -> Result<Vec<TxEnvelope>, BundleError<Db>> {
        let txs = txs
            .iter()
            .map(|tx| TxEnvelope::decode_2718(&mut tx.chunk()))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(txs)
    }

    /// Take the response from the bundle driver. This consumes the driver.
    pub fn into_response(self) -> R {
        self.response
    }

    /// Get a reference to the bundle.
    pub const fn bundle(&self) -> &B {
        &self.bundle
    }

    /// Get a reference to the response.
    pub const fn response(&self) -> &R {
        &self.response
    }
}

impl BundleProcessor<EthCallBundle, EthCallBundleResponse> {
    /// Create a new bundle simulator with the given bundle.
    pub fn new_call(bundle: EthCallBundle) -> Self {
        Self::new(bundle)
    }

    /// Process a bundle transaction and accumulate the results into a [EthCallBundleTransactionResult].
    pub fn process_call_bundle_tx<Db: Database + DatabaseCommit>(
        tx: &TxEnvelope,
        pre_sim_coinbase_balance: U256,
        post_sim_coinbase_balance: U256,
        basefee: u64,
        execution_result: ExecutionResult,
    ) -> Result<(EthCallBundleTransactionResult, U256), BundleError<Db>> {
        let gas_used = execution_result.gas_used();

        // Calculate the gas price
        let gas_price = match tx {
            TxEnvelope::Legacy(tx) => U256::from(tx.tx().gas_price),
            TxEnvelope::Eip2930(tx) => U256::from(tx.tx().gas_price),
            TxEnvelope::Eip1559(tx) => U256::from(tx.tx().effective_gas_price(Some(basefee))),
            TxEnvelope::Eip4844(tx) => match tx.tx() {
                TxEip4844Variant::TxEip4844(tx) => {
                    U256::from(tx.effective_gas_price(Some(basefee)))
                }
                TxEip4844Variant::TxEip4844WithSidecar(tx) => {
                    U256::from(tx.tx.effective_gas_price(Some(basefee)))
                }
            },
            _ => return Err(BundleError::UnsupportedTransactionType),
        };

        // Calculate the gas fees paid
        let gas_fees = match tx {
            TxEnvelope::Legacy(tx) => U256::from(tx.tx().gas_price) * U256::from(gas_used),
            TxEnvelope::Eip2930(tx) => U256::from(tx.tx().gas_price) * U256::from(gas_used),
            TxEnvelope::Eip1559(tx) => {
                U256::from(tx.tx().effective_gas_price(Some(basefee))) * U256::from(gas_used)
            }
            TxEnvelope::Eip4844(tx) => match tx.tx() {
                TxEip4844Variant::TxEip4844(tx) => {
                    U256::from(tx.effective_gas_price(Some(basefee))) * U256::from(gas_used)
                }
                TxEip4844Variant::TxEip4844WithSidecar(tx) => {
                    U256::from(tx.tx.effective_gas_price(Some(basefee))) * U256::from(gas_used)
                }
            },
            _ => return Err(BundleError::UnsupportedTransactionType),
        };

        // set the return data for the response
        let (value, revert) = if execution_result.is_success() {
            let value = execution_result.into_output().unwrap_or_default();
            (Some(value), None)
        } else {
            let revert = execution_result.into_output().unwrap_or_default();
            (None, Some(revert))
        };

        let coinbase_diff = post_sim_coinbase_balance.saturating_sub(pre_sim_coinbase_balance);
        let eth_sent_to_coinbase = coinbase_diff.saturating_sub(gas_fees);

        Ok((
            EthCallBundleTransactionResult {
                tx_hash: *tx.tx_hash(),
                coinbase_diff,
                eth_sent_to_coinbase,
                from_address: tx.recover_signer()?,
                to_address: match tx.kind() {
                    TxKind::Call(to) => Some(to),
                    _ => Some(Address::ZERO),
                },
                value,
                revert,
                gas_used,
                gas_price,
                gas_fees,
            },
            post_sim_coinbase_balance,
        ))
    }
}

impl<Db, Insp> BundleDriver<Db, Insp> for BundleProcessor<EthCallBundle, EthCallBundleResponse>
where
    Db: Database + DatabaseCommit,
    Insp: Inspector<Ctx<Db>>,
{
    type Error = BundleError<Db>;

    fn run_bundle(
        &mut self,
        trevm: crate::EvmNeedsTx<Db, Insp>,
    ) -> DriveBundleResult<Self, Db, Insp> {
        // Check if the block we're in is valid for this bundle. Both must match
        trevm_ensure!(
            trevm.inner().block.number == U256::from(self.bundle.block_number),
            trevm,
            BundleError::BlockNumberMismatch
        );

        // Check if the bundle has any transactions
        trevm_ensure!(!self.bundle.txs.is_empty(), trevm, BundleError::BundleEmpty);

        // Check if the state block number is valid (not 0, and not a tag)
        trevm_ensure!(
            self.bundle.state_block_number.is_number()
                && self.bundle.state_block_number.as_number().unwrap_or(0) != 0,
            trevm,
            BundleError::BlockNumberMismatch
        );

        // Set the state block number this simulation was based on
        self.response.state_block_number =
            self.bundle.state_block_number.as_number().unwrap_or(trevm.block_number().to());

        let bundle_filler = BundleBlockFiller::from(&self.bundle);

        let run_result = trevm.try_with_block(&bundle_filler, |trevm| {
            // We need to keep track of the state of the EVM as we run the transactions, so we can accumulate the results.
            // Therefore we keep this mutable trevm instance, and set it to the new one after we're done simulating.
            let mut trevm = trevm;

            // Decode and validate the transactions in the bundle
            let txs = trevm_try!(Self::decode_and_validate_txs(&self.bundle.txs), trevm);

            // Cache the pre simulation coinbase balance, so we can use it to calculate the coinbase diff after every tx simulated.
            let initial_coinbase_balance = trevm_try!(
                trevm
                    .try_read_balance(trevm.inner().block.beneficiary)
                    .map_err(|e| { BundleError::EVMError { inner: EVMError::Database(e) } }),
                trevm
            );
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

                        // Get the coinbase and basefee from the block
                        let coinbase = committed_trevm.inner().block.beneficiary;
                        let basefee = committed_trevm.inner().block.basefee;

                        // Get the post simulation coinbase balance
                        let post_sim_coinbase_balance = trevm_try!(
                            committed_trevm.try_read_balance(coinbase).map_err(|e| {
                                BundleError::EVMError { inner: EVMError::Database(e) }
                            }),
                            committed_trevm
                        );

                        // Process the transaction and accumulate the results
                        let (response, post_sim_coinbase_balance) = trevm_try!(
                            Self::process_call_bundle_tx(
                                tx,
                                pre_sim_coinbase_balance,
                                post_sim_coinbase_balance,
                                basefee,
                                execution_result
                            ),
                            committed_trevm
                        );

                        // Accumulate overall results from response
                        total_gas_used += response.gas_used;
                        total_gas_fees += response.gas_fees;
                        self.response.results.push(response);
                        hash_bytes.extend_from_slice(tx.tx_hash().as_slice());

                        // update the coinbase balance
                        pre_sim_coinbase_balance = post_sim_coinbase_balance;

                        // Set the trevm instance to the committed one
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

    fn post_bundle(&mut self, _trevm: &crate::EvmNeedsTx<Db, Insp>) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl<Db, Insp> BundleDriver<Db, Insp> for BundleProcessor<EthSendBundle, EthBundleHash>
where
    Db: Database + DatabaseCommit,
    Insp: Inspector<Ctx<Db>>,
{
    type Error = BundleError<Db>;

    fn run_bundle(
        &mut self,
        trevm: crate::EvmNeedsTx<Db, Insp>,
    ) -> DriveBundleResult<Self, Db, Insp> {
        {
            // Check if the block we're in is valid for this bundle. Both must match
            trevm_ensure!(
                trevm.block_number() == U256::from(self.bundle.block_number),
                trevm,
                BundleError::BlockNumberMismatch
            );

            // Check for start timestamp range validity
            if let Some(min_timestamp) = self.bundle.min_timestamp {
                trevm_ensure!(
                    trevm.block_timestamp() >= U256::from(min_timestamp),
                    trevm,
                    BundleError::TimestampOutOfRange
                );
            }

            // Check for end timestamp range validity
            if let Some(max_timestamp) = self.bundle.max_timestamp {
                trevm_ensure!(
                    trevm.block_timestamp() <= U256::from(max_timestamp),
                    trevm,
                    BundleError::TimestampOutOfRange
                );
            }

            // Check if the bundle has any transactions
            trevm_ensure!(!self.bundle.txs.is_empty(), trevm, BundleError::BundleEmpty);

            // Decode and validate the transactions in the bundle
            let txs = trevm_try!(Self::decode_and_validate_txs(&self.bundle.txs), trevm);

            // Store the current evm state in this mutable variable, so we can continually use the freshest state for each simulation
            let mut t = trevm;

            let mut hash_bytes = Vec::with_capacity(32 * txs.len());

            for tx in txs.iter() {
                hash_bytes.extend_from_slice(tx.tx_hash().as_slice());
                // Run the transaction
                let run_result = match t.run_tx(tx) {
                    Ok(res) => res,
                    Err(e) => return Err(e.map_err(|e| BundleError::EVMError { inner: e })),
                };

                // Accept the state if the transaction was successful and the bundle did not revert or halt AND
                // the tx that reverted is NOT in the set of transactions allowed to revert
                let trevm = match run_result.result() {
                    ExecutionResult::Success { .. } => run_result.accept_state(),
                    ExecutionResult::Revert { .. } | ExecutionResult::Halt { .. } => {
                        // If the transaction reverted but it is contained in the set of transactions allowed to revert,
                        // then we _accept_ the state and move on.
                        // See https://github.com/flashbots/rbuilder/blob/52fea312e5d8be1f1405c52d1fd207ecee2d14b1/crates/rbuilder/src/building/order_commit.rs#L546-L558
                        if self.bundle.reverting_tx_hashes.contains(tx.tx_hash()) {
                            run_result.accept_state()
                        } else {
                            trevm_bail!(run_result, BundleError::BundleReverted);
                        }
                    }
                };

                // Make sure to update the trevm instance we're using to simulate with the latest one
                t = trevm;
            }

            // Populate the response, which in this case just means setting the bundle hash
            self.response.bundle_hash = keccak256(hash_bytes);

            Ok(t)
        }
    }

    fn post_bundle(&mut self, _trevm: &crate::EvmNeedsTx<Db, Insp>) -> Result<(), Self::Error> {
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
    fn fill_block_env(&self, block_env: &mut revm::context::block::BlockEnv) {
        if let Some(timestamp) = self.timestamp {
            block_env.timestamp = U256::from(timestamp);
        } else {
            block_env.timestamp += U256::from(12);
        }
        if let Some(gas_limit) = self.gas_limit {
            block_env.gas_limit = gas_limit;
        }
        if let Some(difficulty) = self.difficulty {
            block_env.difficulty = difficulty;
        }
        if let Some(base_fee) = self.base_fee {
            block_env.basefee = base_fee.try_into().unwrap_or(u64::MAX);
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

impl<Db, Insp> BundleDriver<Db, Insp> for EthCallBundle
where
    Db: Database + DatabaseCommit,
    Insp: Inspector<Ctx<Db>>,
{
    type Error = BundleError<Db>;

    fn run_bundle(
        &mut self,
        trevm: crate::EvmNeedsTx<Db, Insp>,
    ) -> DriveBundleResult<Self, Db, Insp> {
        // Check if the block we're in is valid for this bundle. Both must match
        trevm_ensure!(
            trevm.block_number() == U256::from(self.block_number),
            trevm,
            BundleError::BlockNumberMismatch
        );

        // Check if the bundle has any transactions
        trevm_ensure!(!self.txs.is_empty(), trevm, BundleError::BundleEmpty);

        // Check if the state block number is valid (not 0, and not a tag)
        trevm_ensure!(
            self.state_block_number.is_number()
                && self.state_block_number.as_number().unwrap_or(0) != 0,
            trevm,
            BundleError::BlockNumberMismatch
        );

        let bundle_filler = BundleBlockFiller::from(self.clone());

        let run_result = trevm.try_with_block(&bundle_filler, |trevm| {
            let mut trevm = trevm;

            let txs = trevm_try!(
                self.txs
                    .iter()
                    .map(|tx| TxEnvelope::decode_2718(&mut tx.chunk()))
                    .collect::<Result<Vec<_>, _>>(),
                trevm
            );

            // Check that the bundle does not exceed the maximum gas limit for blob transactions
            let mbg = match trevm.spec_id() {
                SpecId::CANCUN => MAX_BLOB_GAS_PER_BLOCK_CANCUN,
                SpecId::PRAGUE => MAX_BLOB_GAS_PER_BLOCK_PRAGUE,
                SpecId::OSAKA => MAX_BLOB_GAS_PER_BLOCK_OSAKA,
                _ => 0,
            };
            trevm_ensure!(
                txs.iter()
                    .filter_map(|tx| tx.as_eip4844())
                    .map(|tx| tx.tx().tx().blob_gas())
                    .sum::<u64>()
                    <= mbg,
                trevm,
                BundleError::Eip4844BlobGasExceeded
            );

            for tx in txs.iter() {
                let run_result = trevm.run_tx(tx);

                match run_result {
                    // return immediately if errored
                    Err(e) => {
                        return Err(e.map_err(|e| BundleError::EVMError { inner: e }));
                    }
                    // Accept the state, and move on
                    Ok(res) => {
                        trevm = res.accept_state();
                    }
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

    fn post_bundle(&mut self, _trevm: &crate::EvmNeedsTx<Db, Insp>) -> Result<(), Self::Error> {
        Ok(())
    }
}

/// An implementation of [BundleDriver] for [EthSendBundle].
/// This allows us to drive a bundle of transactions and accumulate the resulting state in the EVM.
/// Allows to simply take an [EthSendBundle] and get the resulting EVM state.
impl<Db, Insp> BundleDriver<Db, Insp> for EthSendBundle
where
    Db: Database + DatabaseCommit,
    Insp: Inspector<Ctx<Db>>,
{
    type Error = BundleError<Db>;

    fn run_bundle(
        &mut self,
        trevm: crate::EvmNeedsTx<Db, Insp>,
    ) -> DriveBundleResult<Self, Db, Insp> {
        // Check if the block we're in is valid for this bundle. Both must match
        trevm_ensure!(
            trevm.block_number() == U256::from(self.block_number),
            trevm,
            BundleError::BlockNumberMismatch
        );

        // Check for start timestamp range validity

        if let Some(min_timestamp) = self.min_timestamp {
            trevm_ensure!(
                trevm.block_timestamp() >= U256::from(min_timestamp),
                trevm,
                BundleError::TimestampOutOfRange
            );
        }

        // Check for end timestamp range validity
        if let Some(max_timestamp) = self.max_timestamp {
            trevm_ensure!(
                trevm.block_timestamp() <= U256::from(max_timestamp),
                trevm,
                BundleError::TimestampOutOfRange
            );
        }

        // Check if the bundle has any transactions
        trevm_ensure!(!self.txs.is_empty(), trevm, BundleError::BundleEmpty);

        let txs = trevm_try!(
            self.txs
                .iter()
                .map(|tx| TxEnvelope::decode_2718(&mut tx.chunk()))
                .collect::<Result<Vec<_>, _>>(),
            trevm
        );

        // Check that the bundle does not exceed the maximum gas limit for blob transactions

        let mbg = match trevm.spec_id() {
            SpecId::CANCUN => MAX_BLOB_GAS_PER_BLOCK_CANCUN,
            SpecId::PRAGUE => MAX_BLOB_GAS_PER_BLOCK_PRAGUE,
            SpecId::OSAKA => MAX_BLOB_GAS_PER_BLOCK_OSAKA,
            _ => 0,
        };
        trevm_ensure!(
            txs.iter()
                .filter_map(|tx| tx.as_eip4844())
                .map(|tx| tx.tx().tx().blob_gas())
                .sum::<u64>()
                <= mbg,
            trevm,
            BundleError::Eip4844BlobGasExceeded
        );

        // Store the current evm state in this mutable variable, so we can continually use the freshest state for each simulation
        let mut t = trevm;

        for tx in txs.iter() {
            // Run the transaction
            let run_result = match t.run_tx(tx) {
                Ok(res) => res,
                Err(e) => return Err(e.map_err(|e| BundleError::EVMError { inner: e })),
            };

            // Accept the state if the transaction was successful and the bundle did not revert or halt AND
            // the tx that reverted is NOT in the set of transactions allowed to revert
            let trevm = match run_result.result() {
                ExecutionResult::Success { .. } => run_result.accept_state(),
                ExecutionResult::Revert { .. } | ExecutionResult::Halt { .. } => {
                    // If the transaction reverted but it is contained in the set of transactions allowed to revert,
                    // then we _accept_ the state and move on.
                    // See https://github.com/flashbots/rbuilder/blob/52fea312e5d8be1f1405c52d1fd207ecee2d14b1/crates/rbuilder/src/building/order_commit.rs#L546-L558
                    if self.reverting_tx_hashes.contains(tx.tx_hash()) {
                        run_result.accept_state()
                    } else {
                        trevm_bail!(run_result, BundleError::BundleReverted)
                    }
                }
            };

            // Make sure to update the trevm instance we're using to simulate with the latest one
            t = trevm;
        }

        Ok(t)
    }

    fn post_bundle(&mut self, _trevm: &crate::EvmNeedsTx<Db, Insp>) -> Result<(), Self::Error> {
        Ok(())
    }
}
