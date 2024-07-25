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
        Account, AccountInfo, AccountStatus, Bytecode, EVMError, EvmStorageSlot, ExecutionResult,
        ResultAndState, SpecId, BLOCKHASH_SERVE_WINDOW,
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
    pub withdrawals: &'a [Withdrawal],

    /// The block outputs.
    outputs: BlockOutput<ReceiptEnvelope>,
}

impl<'a> From<&'a [Withdrawal]> for Shanghai<'a> {
    fn from(withdrawals: &'a [Withdrawal]) -> Self {
        Self { withdrawals, outputs: Default::default() }
    }
}

impl<Ext, Db: Database + DatabaseCommit> BlockContext<Ext, Db> for Shanghai<'_> {
    type Error = EVMError<Db::Error>;

    fn open_block<B: Block>(
        &mut self,
        evm: &mut Evm<'_, Ext, Db>,
        b: &B,
    ) -> Result<(), Self::Error> {
        if let Some(hint) = b.tx_count_hint() {
            self.outputs.reserve(hint);
        }
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

impl<'a> Shanghai<'a> {
    /// Instantiate a new Shanghai context.
    pub fn new(withdrawals: &'a [Withdrawal]) -> Self {
        Self { withdrawals, outputs: Default::default() }
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
            .withdrawals
            .iter()
            .map(|withdrawal| (withdrawal.address, withdrawal.amount as u128))
            .filter(|(_, amount)| *amount != 0);

        for (address, amount) in increments {
            let mut info = match evm.db_mut().basic(address) {
                Ok(account) => account.unwrap_or_default(),
                Err(error) => return Err(EVMError::Database(error)),
            };
            info.balance = info.balance.saturating_add(U256::from(amount));
            changes.insert(
                address,
                Account { info, status: AccountStatus::Touched, ..Default::default() },
            );
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

impl<'a> Cancun<'a> {
    /// Create a new Cancun context.
    pub fn new(parent_beacon_root: B256, shanghai: Shanghai<'a>) -> Self {
        Self { parent_beacon_root, shanghai }
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
    requests: Vec<Request>,
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

impl<'a> From<Cancun<'a>> for Prague<'a> {
    fn from(cancun: Cancun<'a>) -> Self {
        Self { cancun, requests: Vec::new() }
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
        // ordering is important here as the `find_deposit_logs` method relies
        // on the receipt produced by the inner `after_tx` call.
        self.cancun.after_tx(evm, result);
        self.find_deposit_logs();
    }

    fn close_block<'a>(&mut self, evm: &mut Evm<'_, Ext, Db>) -> Result<(), Self::Error> {
        self.apply_eip7002(evm)?;
        self.apply_eip7251(evm)?;
        self.cancun.close_block(evm)
    }
}

impl<'a> Prague<'a> {
    /// Create a new Prague context.
    pub fn new(cancun: Cancun<'a>) -> Self {
        Self { cancun, requests: Vec::new() }
    }

    /// Get the requests produced in the block.
    pub fn requests(&self) -> &[Request] {
        &self.requests
    }
}

impl Prague<'_> {
    /// Finds deposit logs for the most recent receipt.
    fn find_deposit_logs(&mut self) {
        let receipt =
            self.cancun.shanghai.outputs.receipts().last().expect("produced in shanghai lifecycle");

        for log in receipt
            .logs()
            .iter()
            .filter(|log| log.address == eip6110::MAINNET_DEPOSIT_CONTRACT_ADDRESS)
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

        let Some(output) = res.output() else {
            panic!("execution halted during withdrawal request system contract execution")
        };
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
    ///
    /// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
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
    use crate::{syscall::eip4788::BEACON_ROOTS_ADDRESS, NoopBlock, NoopCfg, TrevmBuilder, Tx};
    use alloy_consensus::constants::{ETH_TO_WEI, GWEI_TO_WEI};
    use alloy_eips::{
        eip7002::WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS,
        eip7251::CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS,
    };
    use alloy_primitives::{fixed_bytes, Address, Bytes, FixedBytes, TxKind, U256};

    use revm::{Evm, InMemoryDB};

    const WITHDRAWALS: &[Withdrawal] = &[Withdrawal {
        validator_index: 1,
        index: 1,
        address: Address::with_last_byte(0x69),
        amount: 100 * GWEI_TO_WEI,
    }];

    // Withdrawal tx
    const WITHDRAWAL_ADDR: Address = Address::with_last_byte(0x42);
    const WITHDRAWAL_AMOUNT: FixedBytes<8> = fixed_bytes!("2222222222222222");
    const VALIDATOR_PUBKEY: FixedBytes<48> = fixed_bytes!("111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111");
    const TARGET_VALIDATOR_PUBKEY: FixedBytes<48> = fixed_bytes!("111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111");

    // TODO: Remove once https://github.com/alloy-rs/alloy/issues/1103 is resolved.
    const CONSOLIDATION_REQUEST_PREDEPLOY_CODE: &str = "3373fffffffffffffffffffffffffffffffffffffffe146098573615156028575f545f5260205ff35b36606014156101445760115f54600182026001905f5b5f82111560595781019083028483029004916001019190603e565b90939004341061014457600154600101600155600354806004026004013381556001015f35815560010160203581556001016040359055600101600355005b6003546002548082038060011160ac575060015b5f5b81811460f15780607402838201600402600401805490600101805490600101805490600101549260601b84529083601401528260340152906054015260010160ae565b9101809214610103579060025561010e565b90505f6002555f6003555b5f548061049d141561011d57505f5b6001546001828201116101325750505f610138565b01600190035b5f555f6001556074025ff35b5f5ffd";

    struct WithdrawalTx;

    impl Tx for WithdrawalTx {
        fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
            // https://github.com/lightclient/7002asm/blob/e0d68e04d15f25057af7b6d180423d94b6b3bdb3/test/Contract.t.sol.in#L49-L64
            let input: Bytes = [&VALIDATOR_PUBKEY[..], &WITHDRAWAL_AMOUNT[..]].concat().into();

            tx_env.caller = WITHDRAWAL_ADDR;
            tx_env.data = input;
            tx_env.transact_to = TxKind::Call(WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS);
            // `MIN_WITHDRAWAL_REQUEST_FEE`
            tx_env.value = U256::from(1);
        }
    }

    struct ConsolidationTx;

    impl Tx for ConsolidationTx {
        fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
            let input: Bytes =
                [&VALIDATOR_PUBKEY[..], &TARGET_VALIDATOR_PUBKEY[..]].concat().into();

            tx_env.caller = WITHDRAWAL_ADDR;
            tx_env.data = input;
            tx_env.transact_to = TxKind::Call(CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS);
            // `MIN_CONSOLIDATION_REQUEST_FEE`
            tx_env.value = U256::from(1);
        }
    }

    fn get_shanghai_context<'a>() -> Shanghai<'a> {
        let outputs = BlockOutput::default();
        let mut withdrawals = Vec::new();

        let withdrawal = Withdrawal {
            validator_index: 1,
            index: 1,
            address: Address::with_last_byte(0x69),
            amount: 100 * GWEI_TO_WEI,
        };

        withdrawals.push(withdrawal);

        Shanghai { withdrawals: WITHDRAWALS, outputs }
    }

    #[test]
    fn test_shanghai_syscall() {
        let mut db = InMemoryDB::default();

        db.insert_account_info(
            Address::with_last_byte(0x69),
            AccountInfo {
                balance: U256::ZERO,
                nonce: 1,
                code: None,
                code_hash: Default::default(),
            },
        );

        let shanghai = get_shanghai_context();

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

    #[test]
    fn test_cancun_syscall() {
        // Pre-cancun setup (Shanghai)
        let mut db = InMemoryDB::default();

        db.insert_account_info(
            Address::with_last_byte(0x69),
            AccountInfo {
                balance: U256::ZERO,
                nonce: 1,
                code: None,
                code_hash: Default::default(),
            },
        );

        let shanghai = get_shanghai_context();

        // Set up cancun
        // 1. Insert the beacon root contract into the EVM
        let bytecode = Bytecode::new_raw(alloy_eips::eip4788::BEACON_ROOTS_CODE.clone());
        let mut beacon_roots_info = AccountInfo {
            nonce: 1,
            code_hash: bytecode.hash_slow(),
            code: Some(bytecode),
            ..Default::default()
        };

        db.insert_contract(&mut beacon_roots_info);
        db.insert_account_info(BEACON_ROOTS_ADDRESS, beacon_roots_info);

        // 2. Set up the Cancun context, by loading the parent beacon root,
        // which we expect to be 0x21 (33).
        let expected_beacon_root = B256::with_last_byte(0x21);
        let cancun = Cancun { parent_beacon_root: expected_beacon_root, shanghai };

        // We expect the root to be stored at timestamp % HISTORY_BUFFER_LENGTH + HISTORY_BUFFER_LENGTH.
        // In this case, 0 % 8192 + 8192 = 8192. quick maffs
        let expected_beacon_root_slot = U256::from(8192);

        let stored_beacon_root = Evm::builder()
            .with_db(db)
            .build_trevm()
            .fill_cfg(&NoopCfg)
            .open_block(&NoopBlock, cancun)
            .unwrap()
            .close_block()
            .unwrap()
            .read_storage(BEACON_ROOTS_ADDRESS, expected_beacon_root_slot);

        assert_eq!(stored_beacon_root, expected_beacon_root.into());
    }

    #[test]
    fn test_prague_syscalls() {
        // Pre-prague setup (Shanghai)
        let mut db = InMemoryDB::default();

        db.insert_account_info(
            Address::with_last_byte(0x69),
            AccountInfo {
                balance: U256::ZERO,
                nonce: 1,
                code: None,
                code_hash: Default::default(),
            },
        );

        let shanghai = get_shanghai_context();

        // Pre-prague setup (Cancun)
        // 1. Insert the beacon root contract into the EVM
        let bytecode = Bytecode::new_raw(alloy_eips::eip4788::BEACON_ROOTS_CODE.clone());
        let mut beacon_roots_info = AccountInfo {
            nonce: 1,
            code_hash: bytecode.hash_slow(),
            code: Some(bytecode),
            ..Default::default()
        };

        db.insert_contract(&mut beacon_roots_info);
        db.insert_account_info(BEACON_ROOTS_ADDRESS, beacon_roots_info);

        // 2. Set up the Cancun context, by loading the parent beacon root,
        // which we expect to be 0x21 (33).
        let expected_beacon_root = B256::with_last_byte(0x21);
        let cancun = Cancun { parent_beacon_root: expected_beacon_root, shanghai };

        // Prague setup
        // 1. Set up EIP-7002 by inserting the withdrawals contract into the EVM
        let bytecode =
            Bytecode::new_raw(alloy_eips::eip7002::WITHDRAWAL_REQUEST_PREDEPLOY_CODE.clone());
        let mut withdrawal_request_info = AccountInfo {
            nonce: 1,
            code_hash: bytecode.hash_slow(),
            code: Some(bytecode),
            ..Default::default()
        };

        db.insert_contract(&mut withdrawal_request_info);
        db.insert_account_info(
            alloy_eips::eip7002::WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS,
            withdrawal_request_info,
        );

        // 2. Insert the consolidation requests contract into the EVM
        let bytecode = Bytecode::new_raw(
            alloy_primitives::hex::decode(CONSOLIDATION_REQUEST_PREDEPLOY_CODE).unwrap().into(),
        );
        let mut consolidation_request_info = AccountInfo {
            nonce: 1,
            code_hash: bytecode.hash_slow(),
            code: Some(bytecode),
            ..Default::default()
        };

        db.insert_contract(&mut consolidation_request_info);
        db.insert_account_info(CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS, consolidation_request_info);

        // 3. Insert an user account, which will send a withdrawal and consolidation request.
        let user_account_info = AccountInfo {
            balance: U256::from(100 * ETH_TO_WEI),
            nonce: 1,
            code: None,
            code_hash: Default::default(),
        };

        db.insert_account_info(WITHDRAWAL_ADDR, user_account_info);

        // 4. Set up the Prague context, by loading the parent beacon root,
        let prague = Prague { cancun, requests: Vec::new() };

        // 5. Set up the EVM along with the Prague context and transactions.
        let evm = Evm::builder()
            .with_db(db)
            .with_spec_id(SpecId::PRAGUE)
            .build_trevm()
            .fill_cfg(&NoopCfg)
            .open_block(&NoopBlock, prague)
            .unwrap()
            .fill_tx(&WithdrawalTx)
            .run()
            .unwrap()
            .accept()
            .fill_tx(&ConsolidationTx)
            .run()
            .unwrap()
            .accept()
            .close_block()
            .unwrap();

        let (prague, _) = evm.take_context();

        // We should have 1 withdrawal request processed by 7002 and one consolidation request processed by 7251.
        assert_eq!(2, prague.requests.len());

        let withdrawal_request = prague.requests[0].as_withdrawal_request().unwrap();

        assert_eq!(withdrawal_request.validator_pubkey, VALIDATOR_PUBKEY);
        assert_eq!(withdrawal_request.source_address, WITHDRAWAL_ADDR);

        let consolidation_request = prague.requests[1].as_consolidation_request().unwrap();

        assert_eq!(consolidation_request.source_address, WITHDRAWAL_ADDR);
        assert_eq!(consolidation_request.source_pubkey, VALIDATOR_PUBKEY);
        assert_eq!(consolidation_request.target_pubkey, TARGET_VALIDATOR_PUBKEY);
    }
}
