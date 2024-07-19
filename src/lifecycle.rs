use crate::{Block, EvmNeedsTx, NeedsBlock, TransactedError, Trevm};
use alloy_eips::eip4895::Withdrawal;
use alloy_primitives::B256;
use revm::{
    primitives::{EVMError, SpecId},
    Database, DatabaseCommit, State,
};

pub trait Lifecycle<'a, Ext, Db: Database + DatabaseCommit> {
    /// Apply pre-block logic, and prep the EVM for the first user transaction.
    fn open_block<EvmState: NeedsBlock, B: Block>(
        &mut self,
        trevm: Trevm<'a, Ext, State<Db>, EvmState>,
        b: &B,
    ) -> Result<EvmNeedsTx<'a, Ext, State<Db>>, TransactedError<'a, Ext, State<Db>>>;

    /// Apply post-block logic and close the block.
    fn close_block(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, State<Db>>,
    ) -> Result<EvmNeedsTx<'a, Ext, State<Db>>, TransactedError<'a, Ext, State<Db>>>;
}

/// Shanghai lifecycle. This applies the [EIP-4895] pre-block system action.
///
/// [EIP-4895]: https://eips.ethereum.org/EIPS/eip-4895
pub struct ShanghaiLifecycle<'a> {
    /// The withdrawals to be processed.
    pub withdrawls: &'a [Withdrawal],
}

impl<'a, Ext, Db: Database + DatabaseCommit> Lifecycle<'a, Ext, Db> for ShanghaiLifecycle<'_> {
    fn open_block<EvmState: NeedsBlock, B: Block>(
        &mut self,
        mut trevm: Trevm<'a, Ext, State<Db>, EvmState>,
        b: &B,
    ) -> Result<EvmNeedsTx<'a, Ext, State<Db>>, TransactedError<'a, Ext, State<Db>>> {
        let flag = trevm.spec_id() >= SpecId::SPURIOUS_DRAGON;
        trevm.inner_mut_unchecked().db_mut().set_state_clear_flag(flag);
        Ok(trevm.fill_block(b))
    }

    fn close_block(
        &mut self,
        mut trevm: EvmNeedsTx<'a, Ext, State<Db>>,
    ) -> Result<EvmNeedsTx<'a, Ext, State<Db>>, TransactedError<'a, Ext, State<Db>>> {
        let increments = self
            .withdrawls
            .iter()
            .map(|withdrawal| (withdrawal.address, withdrawal.amount as u128))
            .filter(|(_, amount)| *amount != 0);

        let db: &mut State<Db> = trevm.inner_mut_unchecked().db_mut();
        match db.increment_balances(increments) {
            Ok(_) => Ok(trevm),
            Err(error) => Err(TransactedError::new(trevm, EVMError::Database(error))),
        }
    }
}

/// Cancun lifecycle. This applies the [EIP-4788] pre-block system action.
///
/// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
pub struct CancunLifecycle<'a> {
    /// The parent beacon root, for the [EIP-4788] pre-block system action.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub parent_beacon_root: B256,

    /// The Cancun lifecycle is a superset of the Shanghai lifecycle.
    pub shanghai: ShanghaiLifecycle<'a>,
}

impl<'a, Ext, Db: Database + DatabaseCommit> Lifecycle<'a, Ext, Db> for CancunLifecycle<'_> {
    fn open_block<EvmState: NeedsBlock, B: Block>(
        &mut self,
        trevm: Trevm<'a, Ext, State<Db>, EvmState>,
        b: &B,
    ) -> Result<EvmNeedsTx<'a, Ext, State<Db>>, TransactedError<'a, Ext, State<Db>>> {
        trevm.fill_block(b).apply_eip4788(self.parent_beacon_root)
    }

    fn close_block(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, State<Db>>,
    ) -> Result<EvmNeedsTx<'a, Ext, State<Db>>, TransactedError<'a, Ext, State<Db>>> {
        self.shanghai.close_block(trevm)
    }
}

/// Cancun lifecycle. This applies the [EIP-4788] and [EIP-2935] pre-block
/// system actions, as well as the [EIP-7002] and [EIP-7251] post-block system
/// actions.
///
/// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
pub struct PragueLifecycle<'a> {
    /// The Prague lifecycle is a superset of the Cancun lifecycle.
    pub cancun: CancunLifecycle<'a>,
}

impl<'a, Ext, Db: Database + DatabaseCommit> Lifecycle<'a, Ext, Db> for PragueLifecycle<'_> {
    fn open_block<EvmState: NeedsBlock, B: Block>(
        &mut self,
        trevm: Trevm<'a, Ext, State<Db>, EvmState>,
        b: &B,
    ) -> Result<EvmNeedsTx<'a, Ext, State<Db>>, TransactedError<'a, Ext, State<Db>>> {
        self.cancun.open_block(trevm, b)?.apply_eip2935()
    }

    fn close_block(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, State<Db>>,
    ) -> Result<EvmNeedsTx<'a, Ext, State<Db>>, TransactedError<'a, Ext, State<Db>>> {
        let trevm = trevm.apply_eip7002()?.apply_eip7251()?;
        self.cancun.close_block(trevm)
    }
}
