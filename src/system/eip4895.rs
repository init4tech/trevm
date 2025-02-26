use crate::{EvmExtUnchecked, EvmNeedsTx};
use alloy::{
    eips::eip4895::Withdrawal,
    primitives::{map::HashMap, U256},
};
use revm::{primitives::EVMError, Database, DatabaseCommit};

impl<Ext, Db: Database + DatabaseCommit> EvmNeedsTx<'_, Ext, Db> {
    /// Apply the withdrawals to the EVM state.
    pub fn apply_withdrawals<'b>(
        &mut self,
        withdrawals: impl IntoIterator<Item = &'b Withdrawal>,
    ) -> Result<(), EVMError<Db::Error>> {
        // We need to apply the withdrawals by incrementing the balances of the
        // respective accounts, then committing the changes to the database.
        let mut changes = HashMap::default();

        let increments = withdrawals
            .into_iter()
            .map(|withdrawal| (withdrawal.address, withdrawal.amount as u128))
            .filter(|(_, amount)| *amount != 0);

        for (address, amount) in increments {
            let mut acct =
                self.inner_mut_unchecked().account(address).map_err(EVMError::Database)?;
            acct.info.balance = acct.info.balance.saturating_add(U256::from(amount));
            acct.mark_touch();
            changes.insert(address, acct);
        }

        self.commit_unchecked(changes);
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use alloy::{
        eips::eip4895::{Withdrawal, GWEI_TO_WEI},
        primitives::{Address, U256},
    };

    use crate::{NoopBlock, NoopCfg};

    const USER: Address = Address::with_last_byte(0x42);

    const WITHDRAWALS: &[Withdrawal] =
        &[Withdrawal { validator_index: 1, index: 1, address: USER, amount: 100 * GWEI_TO_WEI }];

    #[test]
    fn test_eip4895() {
        let mut trevm = crate::test_utils::test_trevm().fill_cfg(&NoopCfg).fill_block(&NoopBlock);

        assert_eq!(trevm.try_read_balance(USER).unwrap(), U256::ZERO);

        trevm.apply_withdrawals(WITHDRAWALS).unwrap();

        assert_eq!(trevm.try_read_balance(USER).unwrap(), U256::from(100 * GWEI_TO_WEI));
    }
}
