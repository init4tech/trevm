use crate::{
    syscall::{eip7002::WITHDRAWAL_REQUEST_BYTES, eip7251::CONSOLIDATION_REQUEST_BYTES, SystemTx},
    Block, EvmNeedsTx, Lifecycle, NeedsBlock, Transacted, TransactedError, Trevm,
};
use alloy_consensus::Request;
use alloy_eips::{
    eip2935::{HISTORY_STORAGE_ADDRESS, HISTORY_STORAGE_CODE},
    eip4895::Withdrawal,
    eip7002::WithdrawalRequest,
    eip7251::ConsolidationRequest,
};
use alloy_primitives::{B256, U256};
use revm::{
    primitives::{
        Account, AccountInfo, Bytecode, EVMError, EvmStorageSlot, SpecId, BLOCKHASH_SERVE_WINDOW,
    },
    Database, DatabaseCommit,
};
use std::collections::HashMap;

/// Lifecycle result type alias.
pub type LifecycleResult<'a, Ext, Db, T> = Result<
    EvmNeedsTx<'a, Ext, Db>,
    TransactedError<'a, Ext, Db, <T as Lifecycle<'a, Ext, Db>>::Error>,
>;

/// Lifecycle result for [`PragueLifecycle`].
pub type PragueLifecycleResult<'a, Ext, Db> = LifecycleResult<'a, Ext, Db, PragueLifecycle<'a>>;

/// Lifecycle result for [`CancunLifecycle`].
pub type CancunLifecycleResult<'a, Ext, Db> = LifecycleResult<'a, Ext, Db, CancunLifecycle<'a>>;

/// Lifecycle result for [`ShanghaiLifecycle`].
pub type ShanghaiLifecycleResult<'a, Ext, Db> = LifecycleResult<'a, Ext, Db, ShanghaiLifecycle<'a>>;

/// Shanghai lifecycle. This applies the [EIP-4895] post-block system action.
///
/// [EIP-4895]: https://eips.ethereum.org/EIPS/eip-4895
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub struct ShanghaiLifecycle<'a> {
    /// The withdrawals to be processed.
    pub withdrawls: &'a [Withdrawal],
}

impl<'a> From<&'a [Withdrawal]> for ShanghaiLifecycle<'a> {
    fn from(withdrawls: &'a [Withdrawal]) -> Self {
        Self { withdrawls }
    }
}

impl<'a, Ext, Db: Database + DatabaseCommit> Lifecycle<'a, Ext, Db> for ShanghaiLifecycle<'_> {
    type Error = EVMError<Db::Error>;

    fn open_block<TrevmState: NeedsBlock, B: Block>(
        &mut self,
        trevm: Trevm<'a, Ext, Db, TrevmState>,
        b: &B,
    ) -> Result<EvmNeedsTx<'a, Ext, Db>, TransactedError<'a, Ext, Db, Self::Error>> {
        Ok(trevm.fill_block(b))
    }

    fn close_block(
        &mut self,
        mut trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> Result<EvmNeedsTx<'a, Ext, Db>, TransactedError<'a, Ext, Db, Self::Error>> {
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
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct CancunLifecycle<'a> {
    /// The parent beacon root, for the [EIP-4788] pre-block system action.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub parent_beacon_root: B256,

    /// The Cancun lifecycle is a superset of the Shanghai lifecycle.
    pub shanghai: ShanghaiLifecycle<'a>,
}

impl<'a, Ext, Db: Database + DatabaseCommit> Lifecycle<'a, Ext, Db> for CancunLifecycle<'_> {
    type Error = EVMError<Db::Error>;

    fn open_block<TrevmState: NeedsBlock, B: Block>(
        &mut self,
        trevm: Trevm<'a, Ext, Db, TrevmState>,
        b: &B,
    ) -> LifecycleResult<'a, Ext, Db, Self> {
        self.apply_eip4788(trevm.fill_block(b))
    }

    fn close_block(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> LifecycleResult<'a, Ext, Db, Self> {
        self.shanghai.close_block(trevm)
    }
}

impl CancunLifecycle<'_> {
    /// Apply a system transaction as specified in [EIP-4788]. The EIP-4788
    /// pre-block action was introduced in Cancun, and calls the beacon root
    /// contract to update the historical beacon root.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn apply_eip4788<'a, Ext, Db>(
        &self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> CancunLifecycleResult<'a, Ext, Db>
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
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct PragueLifecycle<'a> {
    /// The Prague lifecycle is a superset of the Cancun lifecycle.
    pub cancun: CancunLifecycle<'a>,
}

impl<'a, Ext, Db> Lifecycle<'a, Ext, Db> for PragueLifecycle<'_>
where
    Db: Database + DatabaseCommit,
{
    type Error = EVMError<Db::Error>;

    fn open_block<TrevmState: NeedsBlock, B: Block>(
        &mut self,
        trevm: Trevm<'a, Ext, Db, TrevmState>,
        b: &B,
    ) -> PragueLifecycleResult<'a, Ext, Db> {
        Self::apply_eip2935(self.cancun.open_block(trevm, b)?)
    }

    fn close_block(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> PragueLifecycleResult<'a, Ext, Db> {
        let trevm = Self::apply_eip7251(Self::apply_eip7002(trevm)?)?;
        self.cancun.close_block(trevm)
    }
}

impl PragueLifecycle<'_> {
    /// Apply the pre-block logic for [EIP-2935]. This logic was introduced in
    /// Prague and updates historical block hashes in a special system
    /// contract. Unlike other system transactions, this is NOT modeled as a transaction.
    ///
    /// [EIP-2935]: https://eips.ethereum.org/EIPS/eip-2935
    pub fn apply_eip2935<Ext, Db>(
        mut trevm: EvmNeedsTx<'_, Ext, Db>,
    ) -> PragueLifecycleResult<'_, Ext, Db>
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
    pub fn apply_eip7002<Ext, Db>(
        trevm: EvmNeedsTx<'_, Ext, Db>,
    ) -> PragueLifecycleResult<'_, Ext, Db>
    where
        Db: Database + DatabaseCommit,
    {
        if trevm.spec_id() < SpecId::PRAGUE {
            return Ok(trevm);
        }
        let mut res = trevm.execute_system_tx(&SystemTx::eip7002())?;

        // We make assumptions here:
        // - The system transaction never reverts.
        // - The system transaction always has an output.
        // - The system contract produces correct output.
        // - The output is a list of withdrawal requests.
        // - The output does not contain incomplete requests.

        let Some(output) = res.output() else { panic!("no output") };
        let reqs = output
            .chunks_exact(WITHDRAWAL_REQUEST_BYTES)
            .map(|chunk| {
                let mut req: WithdrawalRequest = Default::default();

                req.source_address.copy_from_slice(&chunk[0..20]);
                req.validator_pubkey.copy_from_slice(&chunk[20..68]);
                req.amount = u64::from_be_bytes(chunk[68..76].try_into().unwrap());

                Request::WithdrawalRequest(req)
            })
            .collect();
        res.evm_mut_unchecked().current_output_mut_unchecked().extend_requests(reqs);

        Ok(res.apply_sys())
    }

    /// Apply a system transaction as specified in [EIP-7251]. The EIP-7251
    /// post-block action calls the consolidation request contract to process
    /// consolidation requests.
    pub fn apply_eip7251<Ext, Db>(
        trevm: EvmNeedsTx<'_, Ext, Db>,
    ) -> PragueLifecycleResult<'_, Ext, Db>
    where
        Db: Database + DatabaseCommit,
    {
        if trevm.spec_id() < SpecId::PRAGUE {
            return Ok(trevm);
        }

        let mut res = trevm.execute_system_tx(&SystemTx::eip7251())?;

        // We make assumptions here:
        // - The system transaction never reverts.
        // - The system transaction always has an output.
        // - The system contract produces correct output.
        // - The output is a list of consolidation requests.
        // - The output does not contain incomplete requests.

        let Some(output) = res.output() else { panic!("no output") };
        let reqs = output
            .chunks_exact(CONSOLIDATION_REQUEST_BYTES)
            .map(|chunk| {
                let mut req: ConsolidationRequest = Default::default();

                req.source_address.copy_from_slice(&chunk[0..20]);
                req.source_pubkey.copy_from_slice(&chunk[20..68]);
                req.target_pubkey.copy_from_slice(&chunk[68..116]);

                Request::ConsolidationRequest(req)
            })
            .collect();
        res.evm_mut_unchecked().current_output_mut_unchecked().extend_requests(reqs);

        Ok(res.apply_sys())
    }
}
