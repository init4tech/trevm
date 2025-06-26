use alloy::primitives::{Address, B256, U256};
use revm::{
    context::{ContextTr, Evm},
    primitives::HashMap,
    state::{Account, AccountInfo, Bytecode, EvmState, EvmStorageSlot},
    Database, DatabaseCommit,
};

/// Extension trait for [`revm::context::Evm`] with convenience functions for
/// reading and modifying state.
pub trait EvmExtUnchecked<Db: Database> {
    /// Get a mutable reference to the database.
    fn db_mut_ext(&mut self) -> &mut Db;

    /// Load an account from the database.
    fn account(&mut self, address: Address) -> Result<Account, Db::Error> {
        let info = self.db_mut_ext().basic(address)?;
        let created = info.is_none();
        let mut acct = Account { info: info.unwrap_or_default(), ..Default::default() };
        if created {
            acct.mark_created();
        }
        Ok(acct)
    }

    /// Load a storage slot from an account.
    fn storage(&mut self, address: Address, index: U256) -> Result<U256, Db::Error> {
        self.db_mut_ext().storage(address, index)
    }

    /// Load the bytecode for a contract. Returns empty bytecode if the account
    /// does not currently have contract code.
    fn bytecode(&mut self, code_hash: B256) -> Result<Bytecode, Db::Error> {
        self.db_mut_ext().code_by_hash(code_hash)
    }

    /// Modify multiple accounts with a closure and commit the modified
    /// accounts.
    fn modify_accounts<I, F>(
        &mut self,
        changes: I,
        f: F,
    ) -> Result<HashMap<Address, AccountInfo>, Db::Error>
    where
        I: IntoIterator<Item = Address>,
        F: Fn(&mut AccountInfo),
        Db: DatabaseCommit,
    {
        let mut state = HashMap::default();
        let mut old = HashMap::default();
        for addr in changes.into_iter() {
            let mut acct = self.account(addr)?;
            old.insert(addr, acct.info.clone());
            f(&mut acct.info);
            acct.mark_touch();
            state.insert(addr, acct);
        }
        self.db_mut_ext().commit(state);
        Ok(old)
    }

    /// Modify an account with a closure and commit the modified account.
    fn modify_account<F>(&mut self, addr: Address, f: F) -> Result<AccountInfo, Db::Error>
    where
        F: FnOnce(&mut AccountInfo),
        Db: DatabaseCommit,
    {
        let mut acct = self.account(addr)?;
        let old = acct.info.clone();
        f(&mut acct.info);
        acct.mark_touch();

        let changes: EvmState = [(addr, acct)].into_iter().collect();
        self.db_mut_ext().commit(changes);
        Ok(old)
    }

    /// Set the storage value of an account, returning the previous value.
    fn set_storage(&mut self, address: Address, index: U256, value: U256) -> Result<U256, Db::Error>
    where
        Db: DatabaseCommit,
    {
        let mut acct = self.account(address)?;
        let old = self.storage(address, index)?;

        let change = EvmStorageSlot::new_changed(old, value, 0);
        acct.storage.insert(index, change);
        acct.mark_touch();

        let changes = [(address, acct)].into_iter().collect();
        self.db_mut_ext().commit(changes);
        Ok(old)
    }

    /// Set the bytecode for an account, returns the previous bytecode.
    fn set_bytecode(
        &mut self,
        address: Address,
        bytecode: Bytecode,
    ) -> Result<Option<Bytecode>, Db::Error>
    where
        Db: DatabaseCommit,
    {
        let mut acct = self.account(address)?;
        let old = self.db_mut_ext().code_by_hash(acct.info.code_hash).map(|old| {
            if old.is_empty() {
                None
            } else {
                Some(old)
            }
        })?;
        acct.info.code_hash = bytecode.hash_slow();
        acct.info.code = Some(bytecode);
        acct.mark_touch();

        let changes = [(address, acct)].into_iter().collect();
        self.db_mut_ext().commit(changes);
        Ok(old)
    }

    /// Increase the balance of an account, returning the previous balance.
    fn increase_balance(&mut self, address: Address, amount: U256) -> Result<U256, Db::Error>
    where
        Db: DatabaseCommit,
    {
        self.modify_account(address, |info| info.balance = info.balance.saturating_add(amount))
            .map(|info| info.balance)
    }

    /// Decrease the balance of an account, returning the previous balance.
    fn decrease_balance(&mut self, address: Address, amount: U256) -> Result<U256, Db::Error>
    where
        Db: DatabaseCommit,
    {
        self.modify_account(address, |info| info.balance = info.balance.saturating_sub(amount))
            .map(|info| info.balance)
    }

    /// Set the balance of an account, returning the previous balance.
    fn set_balance(&mut self, address: Address, amount: U256) -> Result<U256, Db::Error>
    where
        Db: DatabaseCommit,
    {
        self.modify_account(address, |info| info.balance = amount).map(|info| info.balance)
    }

    /// Set the nonce of an account, returning the previous nonce.
    fn set_nonce(&mut self, address: Address, nonce: u64) -> Result<u64, Db::Error>
    where
        Db: DatabaseCommit,
    {
        self.modify_account(address, |info| info.nonce = nonce).map(|info| info.nonce)
    }

    /// Increment the nonce of an account, returning the new nonce.
    fn increment_nonce(&mut self, address: Address) -> Result<u64, Db::Error>
    where
        Db: DatabaseCommit,
    {
        self.modify_account(address, |info| info.nonce = info.nonce.saturating_add(1))
            .map(|info| info.nonce)
    }

    /// Decrement the nonce of an account, returning the new nonce.
    fn decrement_nonce(&mut self, address: Address) -> Result<u64, Db::Error>
    where
        Db: DatabaseCommit,
    {
        self.modify_account(address, |info| info.nonce = info.nonce.saturating_sub(1))
            .map(|info| info.nonce)
    }
}

impl<Ctx, Insp, Inst, Prec> EvmExtUnchecked<Ctx::Db> for Evm<Ctx, Insp, Inst, Prec>
where
    Ctx: ContextTr,
{
    fn db_mut_ext(&mut self) -> &mut Ctx::Db {
        self.ctx.db()
    }
}
