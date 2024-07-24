use crate::{
    syscall::{
        eip6110, eip7002::WITHDRAWAL_REQUEST_BYTES, eip7251::CONSOLIDATION_REQUEST_BYTES,
        execute_system_tx, SystemTx,
    },
    Block, BlockContext, BlockOutput,
};
use alloy_consensus::{Receipt, ReceiptEnvelope, Request, TxReceipt};
use alloy_eips::{
    eip2935::{HISTORY_STORAGE_ADDRESS, HISTORY_STORAGE_CODE},
    eip4895::Withdrawal,
    eip7002::WithdrawalRequest,
    eip7251::ConsolidationRequest,
};
use alloy_primitives::{Bloom, Log, B256, U256};
use alloy_sol_types::SolEvent;
use revm::{
    primitives::{
        Account, AccountInfo, Bytecode, EVMError, EvmStorageSlot, ExecutionResult, ResultAndState,
        SpecId, BLOCKHASH_SERVE_WINDOW,
    },
    Database, DatabaseCommit, Evm,
};
use std::{collections::HashMap, sync::OnceLock};

/// A context that performs the fewest meaingful actions. Specifically, it
/// fills the block, and applies transactions to the EVM db. It does not apply
/// any pre- or post-block actions.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub struct BasicContext;

impl<Ext, Db: Database + DatabaseCommit> BlockContext<Ext, Db> for BasicContext {
    type Error = EVMError<Db::Error>;

    fn open_block<B: Block>(
        &mut self,
        evm: &mut Evm<'_, Ext, Db>,
        b: &B,
    ) -> Result<(), Self::Error> {
        b.fill_block(evm);
        Ok(())
    }

    fn after_tx(&mut self, evm: &mut Evm<'_, Ext, Db>, result: revm::primitives::ResultAndState) {
        evm.db_mut().commit(result.state);
    }

    fn close_block(&mut self, _evm: &mut Evm<'_, Ext, Db>) -> Result<(), Self::Error> {
        Ok(())
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

    fn open_block<B: Block>(
        &mut self,
        evm: &mut Evm<'_, Ext, Db>,
        b: &B,
    ) -> Result<(), Self::Error> {
        b.fill_block(evm);
        Ok(())
    }

    fn after_tx(&mut self, evm: &mut Evm<'_, Ext, Db>, result: ResultAndState) {
        let sender = evm.tx().caller;

        let receipt = self.make_receipt(result.result).into();

        let tx_env = evm.tx();

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

        evm.db_mut().commit(result.state);
        self.outputs.push_result(receipt, sender);
    }

    fn close_block(&mut self, evm: &mut Evm<'_, Ext, Db>) -> Result<(), Self::Error> {
        self.apply_withdrawals(evm)?;
        Ok(())
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
    pub fn apply_withdrawals<Ext, Db>(
        &mut self,
        evm: &mut Evm<'_, Ext, Db>,
    ) -> Result<(), <Self as BlockContext<Ext, Db>>::Error>
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
            let mut info = match evm.db_mut().basic(address) {
                Ok(account) => account.unwrap_or_default(),
                Err(error) => return Err(EVMError::Database(error)),
            };
            info.balance = info.balance.saturating_add(U256::from(amount));
            changes.insert(address, Account { info, ..Default::default() });
        }
        evm.db_mut().commit(changes);

        Ok(())
    }

    /// Get the block outputs. This contains receipts and senders.
    pub const fn outputs(&self) -> &BlockOutput {
        &self.outputs
    }

    /// Get the receipts produced in the block.
    pub fn receipts(&self) -> &[ReceiptEnvelope] {
        self.outputs.receipts()
    }

    /// Get the logs produced in the block.
    pub fn logs(&self) -> impl Iterator<Item = &Log> {
        self.outputs.logs()
    }

    /// Calculate the bloom filter for the block.
    pub fn bloom(&self) -> &Bloom {
        static BLOOM: OnceLock<Bloom> = OnceLock::new();

        BLOOM.get_or_init(|| {
            let mut bloom: Bloom = Bloom::default();
            self.outputs.receipts().iter().for_each(|r| bloom.accrue_bloom(&r.bloom()));
            bloom
        })
    }
}

/// Cancun lifecycle. This applies the [EIP-4788] pre-block beacon root update
/// system transact action, as well withdrawals via the [`Shanghai`] context.
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

impl<'a> std::ops::Deref for Cancun<'a> {
    type Target = Shanghai<'a>;

    fn deref(&self) -> &Self::Target {
        &self.shanghai
    }
}

impl<'a> std::ops::DerefMut for Cancun<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.shanghai
    }
}

impl<Ext, Db: Database + DatabaseCommit> BlockContext<Ext, Db> for Cancun<'_> {
    type Error = EVMError<Db::Error>;

    fn open_block<B: Block>(
        &mut self,
        evm: &mut Evm<'_, Ext, Db>,
        b: &B,
    ) -> Result<(), Self::Error> {
        self.shanghai.open_block(evm, b)?;
        self.apply_eip4788(evm)
    }

    fn after_tx(&mut self, evm: &mut Evm<'_, Ext, Db>, result: ResultAndState) {
        self.shanghai.after_tx(evm, result)
    }

    fn close_block(&mut self, evm: &mut Evm<'_, Ext, Db>) -> Result<(), Self::Error> {
        self.shanghai.close_block(evm)
    }
}

impl Cancun<'_> {
    /// Apply a system transaction as specified in [EIP-4788]. The EIP-4788
    /// pre-block action was introduced in Cancun, and calls the beacon root
    /// contract to update the historical beacon root.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn apply_eip4788<Ext, Db>(
        &mut self,
        evm: &mut Evm<'_, Ext, Db>,
    ) -> Result<(), <Self as BlockContext<Ext, Db>>::Error>
    where
        Db: Database + DatabaseCommit,
    {
        if evm.spec_id() < SpecId::CANCUN {
            return Ok(());
        }
        execute_system_tx(evm, &SystemTx::eip4788(self.parent_beacon_root))?;
        Ok(())
    }
}

/// Prague block context. This applies withdrawals via the [Shanghai],
/// beacon root updates via the [`Cancun`] context, the [EIP-7002] post-block
/// withdrawal requests, and the [EIP-7251] post-block consolidation requests.
///
/// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
/// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Prague<'a> {
    /// The Prague context is a superset of the [`Cancun`] context.
    pub cancun: Cancun<'a>,

    /// Requests produced in the block. These include Deposit, Withdrawal, and
    /// Consolidation requests.
    pub requests: Vec<Request>,
}

impl<'a> std::ops::Deref for Prague<'a> {
    type Target = Cancun<'a>;

    fn deref(&self) -> &Self::Target {
        &self.cancun
    }
}

impl<'a> std::ops::DerefMut for Prague<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.cancun
    }
}

impl<Ext, Db> BlockContext<Ext, Db> for Prague<'_>
where
    Db: Database + DatabaseCommit,
{
    type Error = EVMError<Db::Error>;

    fn open_block<'a, B: Block>(
        &mut self,
        evm: &mut Evm<'_, Ext, Db>,
        b: &B,
    ) -> Result<(), Self::Error> {
        self.cancun.open_block(evm, b)?;
        Self::apply_eip2935(evm)
    }

    fn after_tx<'a>(&mut self, evm: &mut Evm<'_, Ext, Db>, result: ResultAndState) {
        self.cancun.after_tx(evm, result);
        self.find_deposit_logs();
    }

    fn close_block<'a>(&mut self, evm: &mut Evm<'_, Ext, Db>) -> Result<(), Self::Error> {
        self.apply_eip7002(evm)?;
        self.apply_eip7251(evm)?;
        self.cancun.close_block(evm)
    }
}

impl Prague<'_> {
    /// Finds deposit logs for the most recent receipt.
    fn find_deposit_logs(&mut self) {
        let receipt =
            self.cancun.shanghai.outputs.receipts().last().expect("produced in shanghai lifecycle");

        for log in
            receipt.logs().iter().filter(|log| log.address == eip6110::MAINNET_DEPOSIT_ADDRESS)
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
    /// contract. Unlike other system actions, this is NOT modeled as a
    /// transaction.
    ///
    /// [EIP-2935]: https://eips.ethereum.org/EIPS/eip-2935
    pub fn apply_eip2935<Ext, Db>(
        evm: &mut Evm<'_, Ext, Db>,
    ) -> Result<(), <Self as BlockContext<Ext, Db>>::Error>
    where
        Db: Database + DatabaseCommit,
    {
        if evm.spec_id() < SpecId::PRAGUE || evm.block().number.is_zero() {
            return Ok(());
        }

        let mut account: Account = match evm.db_mut().basic(HISTORY_STORAGE_ADDRESS) {
            Ok(Some(account)) => account,
            Ok(None) => AccountInfo {
                nonce: 1,
                code: Some(Bytecode::new_raw(HISTORY_STORAGE_CODE.clone())),
                ..Default::default()
            },
            Err(error) => return Err(EVMError::Database(error)),
        }
        .into();

        let block_num = evm.block().number.as_limbs()[0];
        let prev_block = block_num.saturating_sub(1);

        // Update the EVM state with the new value.
        {
            let slot = U256::from(block_num % BLOCKHASH_SERVE_WINDOW as u64);
            let current_hash = match evm.db_mut().storage(HISTORY_STORAGE_ADDRESS, slot) {
                Ok(current_hash) => current_hash,
                Err(error) => return Err(EVMError::Database(error)),
            };
            let parent_block_hash = match evm.db_mut().block_hash(prev_block) {
                Ok(parent_block_hash) => parent_block_hash,
                Err(error) => return Err(EVMError::Database(error)),
            };

            // Insert the state change for the slot
            let value = EvmStorageSlot::new_changed(current_hash, parent_block_hash.into());

            account.storage.insert(slot, value);
        }

        // Mark the account as touched and commit the state change
        account.mark_touch();
        evm.db_mut().commit(HashMap::from([(HISTORY_STORAGE_ADDRESS, account)]));

        Ok(())
    }

    /// Apply a system transaction as specified in [EIP-7002]. The EIP-7002
    /// post-block action was introduced in Prague, and calls the withdrawal
    /// request contract to process withdrawal requests.
    ///
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    pub fn apply_eip7002<Ext, Db>(
        &mut self,

        evm: &mut Evm<'_, Ext, Db>,
    ) -> Result<(), <Self as BlockContext<Ext, Db>>::Error>
    where
        Db: Database + DatabaseCommit,
    {
        if evm.spec_id() < SpecId::PRAGUE {
            return Ok(());
        }
        let res = execute_system_tx(evm, &SystemTx::eip7002())?;

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

        Ok(())
    }

    /// Apply a system transaction as specified in [EIP-7251]. The EIP-7251
    /// post-block action calls the consolidation request contract to process
    /// consolidation requests.
    pub fn apply_eip7251<Ext, Db>(
        &mut self,
        evm: &mut Evm<'_, Ext, Db>,
    ) -> Result<(), <Self as BlockContext<Ext, Db>>::Error>
    where
        Db: Database + DatabaseCommit,
    {
        if evm.spec_id() < SpecId::PRAGUE {
            return Ok(());
        }

        let res = execute_system_tx(evm, &SystemTx::eip7251())?;

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

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{NoopBlock, NoopCfg, TrevmBuilder};
    use alloy_consensus::constants::GWEI_TO_WEI;
    use alloy_primitives::{Address, U256};

    use revm::{Evm, InMemoryDB};

    #[test]
    fn test_shanghai_syscall() {
        let mut db = InMemoryDB::default();
        let mut withdrawals = Vec::new();
        let outputs = BlockOutput::default();

        db.insert_account_info(
            Address::with_last_byte(0x69),
            AccountInfo {
                balance: U256::ZERO,
                nonce: 1,
                code: None,
                code_hash: Default::default(),
            },
        );

        let withdrawal = Withdrawal {
            validator_index: 1,
            index: 1,
            address: Address::with_last_byte(0x69),
            amount: 100 * GWEI_TO_WEI,
        };

        withdrawals.push(withdrawal);

        let shanghai = Shanghai { withdrawls: &withdrawals, outputs };

        let balance = Evm::builder()
            .with_db(db)
            .build_trevm()
            .fill_cfg(&NoopCfg)
            .open_block(&NoopBlock, shanghai)
            .unwrap()
            .close_block()
            .unwrap()
            .read_balance(Address::with_last_byte(0x69));

        assert_eq!(balance, U256::from(100 * GWEI_TO_WEI));
    }
}
