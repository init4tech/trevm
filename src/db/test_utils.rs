use alloy::primitives::{Address, U256};
use revm::{
    bytecode::Bytecode,
    database::{Database, DatabaseCommit, TryDatabaseCommit},
    primitives::HashMap,
    state::{Account, AccountInfo, AccountStatus, EvmStorageSlot},
};

/// Test utilities for databases.
#[doc(hidden)]
pub trait DbTestExt: Database + DatabaseCommit {
    /// Modify an account via closure, creating it if it doesn't exist.
    fn test_modify_account<F>(&mut self, address: Address, f: F)
    where
        F: FnOnce(&mut AccountInfo),
    {
        let original_info = self.basic(address).ok().flatten().unwrap_or_default();
        let mut info = original_info.clone();
        f(&mut info);
        let account = Account {
            info,
            original_info: Box::new(original_info),
            storage: Default::default(),
            status: AccountStatus::Touched,
            transaction_id: 0,
        };
        self.commit(HashMap::from_iter([(address, account)]));
    }

    /// Set account balance.
    fn test_set_balance(&mut self, address: Address, balance: U256) {
        self.test_modify_account(address, |info| info.balance = balance);
    }

    /// Increase account balance (saturating).
    fn test_increase_balance(&mut self, address: Address, amount: U256) {
        self.test_modify_account(address, |info| {
            info.balance = info.balance.saturating_add(amount)
        });
    }

    /// Decrease account balance (saturating).
    fn test_decrease_balance(&mut self, address: Address, amount: U256) {
        self.test_modify_account(address, |info| {
            info.balance = info.balance.saturating_sub(amount)
        });
    }

    /// Set account nonce.
    fn test_set_nonce(&mut self, address: Address, nonce: u64) {
        self.test_modify_account(address, |info| info.nonce = nonce);
    }

    /// Set a storage slot.
    fn test_set_storage(&mut self, address: Address, slot: U256, value: U256) {
        let info = self.basic(address).ok().flatten().unwrap_or_default();
        let storage =
            HashMap::from_iter([(slot, EvmStorageSlot::new_changed(U256::ZERO, value, 0))]);
        let account = Account {
            info: info.clone(),
            original_info: Box::new(info),
            storage,
            status: AccountStatus::Touched,
            transaction_id: 0,
        };
        self.commit(HashMap::from_iter([(address, account)]));
    }

    /// Set account bytecode.
    fn test_set_bytecode(&mut self, address: Address, bytecode: Bytecode) {
        self.test_modify_account(address, |info| {
            info.code_hash = bytecode.hash_slow();
            info.code = Some(bytecode);
        });
    }
}

impl<Db: Database + DatabaseCommit> DbTestExt for Db {}

/// Test utilities for databases that support fallible commits.
#[doc(hidden)]
pub trait TryDbTestExt: Database + TryDatabaseCommit {
    /// Modify an account via closure, creating it if it doesn't exist.
    fn test_try_modify_account<F>(
        &mut self,
        address: Address,
        f: F,
    ) -> Result<(), <Self as TryDatabaseCommit>::Error>
    where
        F: FnOnce(&mut AccountInfo),
    {
        let original_info = self.basic(address).ok().flatten().unwrap_or_default();
        let mut info = original_info.clone();
        f(&mut info);
        let account = Account {
            info,
            original_info: Box::new(original_info),
            storage: Default::default(),
            status: AccountStatus::Touched,
            transaction_id: 0,
        };
        self.try_commit(HashMap::from_iter([(address, account)]))
    }

    /// Set account balance.
    fn test_try_set_balance(
        &mut self,
        address: Address,
        balance: U256,
    ) -> Result<(), <Self as TryDatabaseCommit>::Error> {
        self.test_try_modify_account(address, |info| info.balance = balance)
    }

    /// Increase account balance (saturating).
    fn test_try_increase_balance(
        &mut self,
        address: Address,
        amount: U256,
    ) -> Result<(), <Self as TryDatabaseCommit>::Error> {
        self.test_try_modify_account(address, |info| {
            info.balance = info.balance.saturating_add(amount)
        })
    }

    /// Decrease account balance (saturating).
    fn test_try_decrease_balance(
        &mut self,
        address: Address,
        amount: U256,
    ) -> Result<(), <Self as TryDatabaseCommit>::Error> {
        self.test_try_modify_account(address, |info| {
            info.balance = info.balance.saturating_sub(amount)
        })
    }

    /// Set account nonce.
    fn test_try_set_nonce(
        &mut self,
        address: Address,
        nonce: u64,
    ) -> Result<(), <Self as TryDatabaseCommit>::Error> {
        self.test_try_modify_account(address, |info| info.nonce = nonce)
    }

    /// Set a storage slot.
    fn test_try_set_storage(
        &mut self,
        address: Address,
        slot: U256,
        value: U256,
    ) -> Result<(), <Self as TryDatabaseCommit>::Error> {
        let info = self.basic(address).ok().flatten().unwrap_or_default();
        let storage =
            HashMap::from_iter([(slot, EvmStorageSlot::new_changed(U256::ZERO, value, 0))]);
        let account = Account {
            info: info.clone(),
            original_info: Box::new(info),
            storage,
            status: AccountStatus::Touched,
            transaction_id: 0,
        };
        self.try_commit(HashMap::from_iter([(address, account)]))
    }

    /// Set account bytecode.
    fn test_try_set_bytecode(
        &mut self,
        address: Address,
        bytecode: Bytecode,
    ) -> Result<(), <Self as TryDatabaseCommit>::Error> {
        self.test_try_modify_account(address, |info| {
            info.code_hash = bytecode.hash_slow();
            info.code = Some(bytecode);
        })
    }
}

impl<Db: Database + TryDatabaseCommit> TryDbTestExt for Db {}
