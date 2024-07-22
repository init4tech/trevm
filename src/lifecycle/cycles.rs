use crate::{Block, EvmNeedsTx, Lifecycle, NeedsBlock, TransactedError, Trevm};
use alloy_eips::eip4895::Withdrawal;
use alloy_primitives::{B256, U256};
use revm::{
    primitives::{Account, EVMError},
    Database, DatabaseCommit,
};
use std::collections::HashMap;

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
    ) -> Result<EvmNeedsTx<'a, Ext, Db>, TransactedError<'a, Ext, Db, Self::Error>> {
        trevm.fill_block(b).apply_eip4788(self.parent_beacon_root)
    }

    fn close_block(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> Result<EvmNeedsTx<'a, Ext, Db>, TransactedError<'a, Ext, Db, Self::Error>> {
        self.shanghai.close_block(trevm)
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

impl<'a, Ext, Db: Database + DatabaseCommit> Lifecycle<'a, Ext, Db> for PragueLifecycle<'_> {
    type Error = EVMError<Db::Error>;

    fn open_block<TrevmState: NeedsBlock, B: Block>(
        &mut self,
        trevm: Trevm<'a, Ext, Db, TrevmState>,
        b: &B,
    ) -> Result<EvmNeedsTx<'a, Ext, Db>, TransactedError<'a, Ext, Db, Self::Error>> {
        self.cancun.open_block(trevm, b)?.apply_eip2935()
    }

    fn close_block(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> Result<EvmNeedsTx<'a, Ext, Db>, TransactedError<'a, Ext, Db, Self::Error>> {
        let trevm = trevm.apply_eip7002()?.apply_eip7251()?;
        self.cancun.close_block(trevm)
    }
}
