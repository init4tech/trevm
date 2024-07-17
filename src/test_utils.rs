use crate::{EvmNeedsCfg, Trevm, TrevmBuilder};
use alloy_primitives::{Address, U256};
use revm::{
    db::{CacheDB, DbAccount, EmptyDB, InMemoryDB},
    inspector_handle_register,
    primitives::{AccountInfo, Bytecode},
    Database, EvmBuilder, GetInspector,
};

pub use revm::test_utils as revm_test_utils;

impl<'a, Ext, Db: Database, State> Trevm<'a, Ext, Db, State> {
    /// Make a new [`Trevm`] with a [`InMemoryDB`].
    pub fn test_trevm() -> EvmNeedsCfg<'static, (), InMemoryDB> {
        test_trevm()
    }

    pub fn test_trevm_with_funds<'b, I>(i: I) -> EvmNeedsCfg<'static, (), InMemoryDB>
    where
        I: IntoIterator<Item = &'b (Address, U256)>,
    {
        let mut trevm = test_trevm();

        for (address, amount) in i {
            trevm.test_set_balance(*address, *amount);
        }

        trevm
    }
}

impl<'a, Ext, State> Trevm<'a, Ext, InMemoryDB, State> {
    /// Modify an account with the provide closure. Returns the original
    /// account info
    pub fn test_modify_account<F>(&mut self, address: Address, f: F) -> AccountInfo
    where
        F: FnOnce(&mut AccountInfo),
    {
        let db = self.inner_mut_unchecked().db_mut();

        let mut acct = db.accounts.get(&address).and_then(DbAccount::info).unwrap_or_default();
        let old = acct.clone();

        f(&mut acct);
        db.insert_account_info(address, acct);

        old
    }

    /// Set the nonce of an account, returning the previous nonce.
    pub fn test_set_nonce(&mut self, address: Address, nonce: u64) -> u64 {
        self.test_modify_account(address, |info| info.nonce = nonce).nonce
    }

    /// Set the EVM storage at a slot.
    pub fn test_set_storage(&mut self, address: Address, slot: U256, value: U256) -> U256 {
        let db: &mut InMemoryDB = self.inner_mut_unchecked().db_mut();

        db.accounts.entry(address).or_default().storage.insert(slot, value).unwrap_or_default()
    }

    /// Set the bytecode at a specific address, returning the previous bytecode
    /// at that address.
    pub fn test_set_bytecode(&mut self, address: Address, bytecode: Bytecode) -> Option<&Bytecode> {
        let hash = bytecode.hash_slow();
        let old_hash = self.test_modify_account(address, |acct| acct.code_hash = hash).code_hash;

        let db: &mut InMemoryDB = self.inner_mut_unchecked().db_mut();
        db.contracts.insert(hash, bytecode);
        db.contracts.get(&old_hash)
    }

    /// Increase the balance of an account. Returns the previous balance.
    pub fn test_increase_balance(&mut self, address: Address, amount: U256) -> U256 {
        self.test_modify_account(address, |acct| acct.balance = acct.balance.saturating_add(amount))
            .balance
    }

    /// Set the balance of an account. Returns the previous balance.
    pub fn test_set_balance(&mut self, address: Address, amount: U256) -> U256 {
        self.test_modify_account(address, |acct| acct.balance = amount).balance
    }
}

/// Make a new [`Trevm`] with the given inspector and an in-memory database.
pub fn test_trevm_with_inspector<I>(inspector: I) -> EvmNeedsCfg<'static, I, CacheDB<EmptyDB>>
where
    I: GetInspector<InMemoryDB>,
{
    EvmBuilder::default()
        .with_db(CacheDB::new(EmptyDB::default()))
        .with_external_context(inspector)
        .append_handler_register(inspector_handle_register)
        .build_trevm()
}

/// Make a new [`Trevm`] with an in-memory database.
pub fn test_trevm() -> EvmNeedsCfg<'static, (), CacheDB<EmptyDB>> {
    EvmBuilder::default().with_db(CacheDB::new(EmptyDB::default())).build_trevm()
}
