use crate::{
    syscall::{
        eip6110, eip7002::WITHDRAWAL_REQUEST_BYTES, eip7251::CONSOLIDATION_REQUEST_BYTES, SystemTx,
    },
    Block, BlockContext, BlockOutput, EvmNeedsTx, NeedsBlock, Transacted, TransactedError, Trevm,
};
use alloy_consensus::{Receipt, ReceiptEnvelope, Request};
use alloy_eips::{
    eip2935::{HISTORY_STORAGE_ADDRESS, HISTORY_STORAGE_CODE},
    eip4895::Withdrawal,
    eip7002::WithdrawalRequest,
    eip7251::ConsolidationRequest,
};
use alloy_primitives::{B256, U256};
use alloy_sol_types::SolEvent;
use revm::{
    primitives::{
        Account, AccountInfo, Bytecode, EVMError, EvmStorageSlot, ExecutionResult, SpecId,
        BLOCKHASH_SERVE_WINDOW,
    },
    Database, DatabaseCommit,
};
use std::collections::HashMap;

/// Lifecycle result type alias.
pub type ContextResult<'a, Ext, Db, T> = Result<
    EvmNeedsTx<'a, Ext, Db>,
    TransactedError<'a, Ext, Db, <T as BlockContext<Ext, Db>>::Error>,
>;

/// Lifecycle result for [`PragueLifecycle`].
pub type PragueContextResult<'a, Ext, Db> = ContextResult<'a, Ext, Db, Prague<'a>>;

/// Lifecycle result for [`CancunLifecycle`].
pub type CancunContextResult<'a, Ext, Db> = ContextResult<'a, Ext, Db, Cancun<'a>>;

/// Lifecycle result for [`ShanghaiLifecycle`].
pub type ShanghaiContextResult<'a, Ext, Db> = ContextResult<'a, Ext, Db, Shanghai<'a>>;

pub struct NoopContext;

impl<Ext, Db: Database + DatabaseCommit> BlockContext<Ext, Db> for NoopContext {
    type Error = EVMError<Db::Error>;

    fn open_block<'a, TrevmState: NeedsBlock, B: Block>(
        &mut self,
        trevm: Trevm<'a, Ext, Db, TrevmState>,
        b: &B,
    ) -> ContextResult<'a, Ext, Db, Self> {
        Ok(trevm.fill_block(b))
    }

    fn apply_tx<'a>(&mut self, trevm: Transacted<'a, Ext, Db>) -> ContextResult<'a, Ext, Db, Self> {
        let (mut trevm, result) = trevm.into_parts();

        trevm.commit_unchecked(result.state);
        Ok(trevm)
    }

    fn close_block<'a>(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> ContextResult<'a, Ext, Db, Self> {
        Ok(trevm)
    }
}

/// Shanghai lifecycle. This applies the [EIP-4895] post-block system action.
///
/// [EIP-4895]: https://eips.ethereum.org/EIPS/eip-4895
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Shanghai<'a> {
    /// The withdrawals to be processed.
    pub withdrawls: &'a [Withdrawal],

    /// The block outputs.
    pub outputs: BlockOutput<ReceiptEnvelope>,
}

impl<'a> From<&'a [Withdrawal]> for Shanghai<'a> {
    fn from(withdrawls: &'a [Withdrawal]) -> Self {
        Self { withdrawls, outputs: Default::default() }
    }
}

impl<Ext, Db: Database + DatabaseCommit> BlockContext<Ext, Db> for Shanghai<'_> {
    type Error = EVMError<Db::Error>;

    fn open_block<'a, TrevmState: NeedsBlock, B: Block>(
        &mut self,
        trevm: Trevm<'a, Ext, Db, TrevmState>,
        b: &B,
    ) -> Result<EvmNeedsTx<'a, Ext, Db>, TransactedError<'a, Ext, Db, Self::Error>> {
        Ok(trevm.fill_block(b))
    }

    fn apply_tx<'a>(
        &mut self,
        trevm: Transacted<'a, Ext, Db>,
    ) -> ShanghaiContextResult<'a, Ext, Db> {
        let sender = trevm.evm().inner().tx().caller;

        let (mut trevm, result) = trevm.into_parts();
        let receipt = self.make_receipt(result.result).into();

        let tx_env = trevm.inner().tx();

        // Determine the receipt envelope type based on the transaction type.
        let receipt = if !tx_env.blob_hashes.is_empty() {
            ReceiptEnvelope::Eip4844(receipt)
        } else if tx_env.gas_priority_fee.is_some() {
            ReceiptEnvelope::Eip1559(receipt)
        } else if !tx_env.access_list.is_empty() {
            ReceiptEnvelope::Eip2930(receipt)
        } else {
            ReceiptEnvelope::Legacy(receipt)
        };

        trevm.commit_unchecked(result.state);
        self.outputs.push_result(receipt, sender);

        Ok(trevm)
    }

    fn close_block<'a>(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> Result<EvmNeedsTx<'a, Ext, Db>, TransactedError<'a, Ext, Db, Self::Error>> {
        self.apply_withdrawals(trevm)
    }
}

impl Shanghai<'_> {
    /// Cumulative gas used in the block so far.
    pub fn cumulative_gas_used(&self) -> u128 {
        self.outputs.cumulative_gas_used()
    }

    /// Make a receipt from the execution result.
    pub fn make_receipt(&self, result: ExecutionResult) -> Receipt {
        let cumulative_gas_used =
            self.cumulative_gas_used().saturating_add(result.gas_used() as u128);
        Receipt {
            status: result.is_success().into(),
            cumulative_gas_used,
            logs: result.into_logs(),
        }
    }

    /// Apply the withdrawals to the EVM state.
    pub fn apply_withdrawals<'a, Ext, Db>(
        &mut self,
        mut trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> ShanghaiContextResult<'a, Ext, Db>
    where
        Db: Database + DatabaseCommit,
    {
        // We need to apply the withdrawals by incrementing the balances of the
        // respective accounts, then committing the changes to the database.
        let mut changes = HashMap::new();

        let increments = self
            .withdrawls
            .iter()
            .map(|withdrawal| (withdrawal.address, withdrawal.amount as u128))
            .filter(|(_, amount)| *amount != 0);

        for (address, amount) in increments {
            let mut info = match trevm.inner_mut_unchecked().db_mut().basic(address) {
                Ok(account) => account.unwrap_or_default(),
                Err(error) => return Err(TransactedError::new(trevm, EVMError::Database(error))),
            };
            info.balance = info.balance.saturating_add(U256::from(amount));
            changes.insert(address, Account { info, ..Default::default() });
        }
        trevm.inner_mut_unchecked().db_mut().commit(changes);

        Ok(trevm)
    }
}

/// Cancun lifecycle. This applies the [EIP-4788] pre-block beacon root update
/// system transact action, as well withdrawals via the [ShanghaiLifecycle].
///
/// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cancun<'a> {
    /// The parent beacon root, for the [EIP-4788] pre-block system action.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub parent_beacon_root: B256,

    /// The Cancun lifecycle is a superset of the Shanghai lifecycle.
    pub shanghai: Shanghai<'a>,
}

impl<Ext, Db: Database + DatabaseCommit> BlockContext<Ext, Db> for Cancun<'_> {
    type Error = EVMError<Db::Error>;

    fn open_block<'a, TrevmState: NeedsBlock, B: Block>(
        &mut self,
        trevm: Trevm<'a, Ext, Db, TrevmState>,
        b: &B,
    ) -> CancunContextResult<'a, Ext, Db> {
        self.apply_eip4788(trevm.fill_block(b))
    }

    fn apply_tx<'a>(&mut self, trevm: Transacted<'a, Ext, Db>) -> CancunContextResult<'a, Ext, Db> {
        self.shanghai.apply_tx(trevm)
    }

    fn close_block<'a>(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> CancunContextResult<'a, Ext, Db> {
        self.shanghai.close_block(trevm)
    }
}

impl Cancun<'_> {
    /// Apply a system transaction as specified in [EIP-4788]. The EIP-4788
    /// pre-block action was introduced in Cancun, and calls the beacon root
    /// contract to update the historical beacon root.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn apply_eip4788<'a, Ext, Db>(
        &self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> CancunContextResult<'a, Ext, Db>
    where
        Db: Database + DatabaseCommit,
    {
        if trevm.spec_id() < SpecId::CANCUN {
            return Ok(trevm);
        }
        trevm
            .execute_system_tx(&SystemTx::eip4788(self.parent_beacon_root))
            .map(Transacted::apply_sys)
    }
}

/// Prague lifecycle. This applies withdrawals via the [ShanghaiLifecycle],
/// beacon root updates via the [CancunLifecycle], the [EIP-7002] post-block
/// withdrawal requests, and the [EIP-7251] post-block consolidation requests.
///
/// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
/// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Prague<'a> {
    /// The Prague lifecycle is a superset of the Cancun lifecycle.
    pub cancun: Cancun<'a>,

    /// Requests produced in the block. These include Deposit, Withdrawal, and
    /// Consolidation requests.
    pub requests: Vec<Request>,
}

impl<Ext, Db> BlockContext<Ext, Db> for Prague<'_>
where
    Db: Database + DatabaseCommit,
{
    type Error = EVMError<Db::Error>;

    fn open_block<'a, TrevmState: NeedsBlock, B: Block>(
        &mut self,
        trevm: Trevm<'a, Ext, Db, TrevmState>,
        b: &B,
    ) -> PragueContextResult<'a, Ext, Db> {
        Self::apply_eip2935(self.cancun.open_block(trevm, b)?)
    }

    fn apply_tx<'a>(&mut self, trevm: Transacted<'a, Ext, Db>) -> PragueContextResult<'a, Ext, Db> {
        let trevm = self.cancun.shanghai.apply_tx(trevm)?;
        self.find_deposit_logs();
        Ok(trevm)
    }

    fn close_block<'a>(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> PragueContextResult<'a, Ext, Db> {
        let trevm = self.apply_eip7002(trevm)?;
        let trevm = self.apply_eip7251(trevm)?;
        self.cancun.close_block(trevm)
    }
}

impl Prague<'_> {
    fn find_deposit_logs(&mut self) {
        let receipt =
            self.cancun.shanghai.outputs.receipts().last().expect("produced in shanghai lifecycle");

        for log in
            receipt.logs().into_iter().filter(|log| log.address == eip6110::MAINNET_DEPOSIT_ADDRESS)
        {
            // We assume that the log is valid because it was emitted by the
            // deposit contract.
            let decoded_log = eip6110::DepositEvent::decode_log(log, false).expect("invalid log");
            let deposit = eip6110::parse_deposit_from_log(&decoded_log);
            self.requests.push(Request::DepositRequest(deposit));
        }
    }

    /// Apply the pre-block logic for [EIP-2935]. This logic was introduced in
    /// Prague and updates historical block hashes in a special system
    /// contract. Unlike other system transactions, this is NOT modeled as a transaction.
    ///
    /// [EIP-2935]: https://eips.ethereum.org/EIPS/eip-2935
    pub fn apply_eip2935<Ext, Db>(
        mut trevm: EvmNeedsTx<'_, Ext, Db>,
    ) -> PragueContextResult<'_, Ext, Db>
    where
        Db: Database + DatabaseCommit,
    {
        if trevm.spec_id() < SpecId::PRAGUE || trevm.inner().block().number.is_zero() {
            return Ok(trevm);
        }

        let mut account: Account =
            match trevm.inner_mut_unchecked().db_mut().basic(HISTORY_STORAGE_ADDRESS) {
                Ok(Some(account)) => account,
                Ok(None) => AccountInfo {
                    nonce: 1,
                    code: Some(Bytecode::new_raw(HISTORY_STORAGE_CODE.clone())),
                    ..Default::default()
                },
                Err(error) => return Err(TransactedError::new(trevm, EVMError::Database(error))),
            }
            .into();

        let block_num = trevm.inner().block().number.as_limbs()[0];
        let prev_block = block_num.saturating_sub(1);

        // Update the EVM state with the new value.
        {
            let slot = U256::from(block_num % BLOCKHASH_SERVE_WINDOW as u64);
            let current_hash =
                match trevm.inner_mut_unchecked().db_mut().storage(HISTORY_STORAGE_ADDRESS, slot) {
                    Ok(current_hash) => current_hash,
                    Err(error) => {
                        return Err(TransactedError::new(trevm, EVMError::Database(error)))
                    }
                };
            let parent_block_hash =
                match trevm.inner_mut_unchecked().db_mut().block_hash(prev_block) {
                    Ok(parent_block_hash) => parent_block_hash,
                    Err(error) => {
                        return Err(TransactedError::new(trevm, EVMError::Database(error)))
                    }
                };

            // Insert the state change for the slot
            let value = EvmStorageSlot::new_changed(current_hash, parent_block_hash.into());

            account.storage.insert(slot, value);
        }

        // Mark the account as touched and commit the state change
        account.mark_touch();
        trevm
            .inner_mut_unchecked()
            .db_mut()
            .commit(HashMap::from([(HISTORY_STORAGE_ADDRESS, account)]));

        Ok(trevm)
    }

    /// Apply a system transaction as specified in [EIP-7002]. The EIP-7002
    /// post-block action was introduced in Prague, and calls the withdrawal
    /// request contract to process withdrawal requests.
    ///
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    pub fn apply_eip7002<'a, Ext, Db>(
        &mut self,

        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> PragueContextResult<'a, Ext, Db>
    where
        Db: Database + DatabaseCommit,
    {
        if trevm.spec_id() < SpecId::PRAGUE {
            return Ok(trevm);
        }
        let res = trevm.execute_system_tx(&SystemTx::eip7002())?;

        // We make assumptions here:
        // - The system transaction never reverts.
        // - The system transaction always has an output.
        // - The system contract produces correct output.
        // - The output is a list of withdrawal requests.
        // - The output does not contain incomplete requests.

        let Some(output) = res.output() else { panic!("no output") };
        self.requests.extend(output.chunks_exact(WITHDRAWAL_REQUEST_BYTES).map(|chunk| {
            let mut req: WithdrawalRequest = Default::default();

            req.source_address.copy_from_slice(&chunk[0..20]);
            req.validator_pubkey.copy_from_slice(&chunk[20..68]);
            req.amount = u64::from_be_bytes(chunk[68..76].try_into().unwrap());

            Request::WithdrawalRequest(req)
        }));

        Ok(res.apply_sys())
    }

    /// Apply a system transaction as specified in [EIP-7251]. The EIP-7251
    /// post-block action calls the consolidation request contract to process
    /// consolidation requests.
    pub fn apply_eip7251<'a, Ext, Db>(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> PragueContextResult<'a, Ext, Db>
    where
        Db: Database + DatabaseCommit,
    {
        if trevm.spec_id() < SpecId::PRAGUE {
            return Ok(trevm);
        }

        let res = trevm.execute_system_tx(&SystemTx::eip7251())?;

        // We make assumptions here:
        // - The system transaction never reverts.
        // - The system transaction always has an output.
        // - The system contract produces correct output.
        // - The output is a list of consolidation requests.
        // - The output does not contain incomplete requests.

        let Some(output) = res.output() else { panic!("no output") };
        self.requests.extend(output.chunks_exact(CONSOLIDATION_REQUEST_BYTES).map(|chunk| {
            let mut req: ConsolidationRequest = Default::default();

            req.source_address.copy_from_slice(&chunk[0..20]);
            req.source_pubkey.copy_from_slice(&chunk[20..68]);
            req.target_pubkey.copy_from_slice(&chunk[68..116]);

            Request::ConsolidationRequest(req)
        }));

        Ok(res.apply_sys())
    }
}
