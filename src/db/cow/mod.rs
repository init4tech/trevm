use crate::db::CachingDb;
use alloy::{
    consensus::constants::KECCAK_EMPTY,
    primitives::{Address, B256, U256},
};
use revm::{
    bytecode::Bytecode,
    database::{in_memory_db::Cache, AccountState, DbAccount},
    primitives::HashMap,
    state::{Account, AccountInfo},
    Database, DatabaseCommit, DatabaseRef,
};

use super::TryCachingDb;

/// A version of [`CacheDB`] that caches only on write, not on read.
///
/// This saves memory when wrapping some other caching database, like [`State`]
/// or [`ConcurrentState`].
///
/// [`CacheDB`]: revm::database::in_memory_db::CacheDB
/// [`State`]: revm::database::State
/// [`ConcurrentState`]: crate::db::sync::ConcurrentState
#[derive(Debug)]
pub struct CacheOnWrite<Db> {
    cache: Cache,
    inner: Db,
}

impl<Db> Default for CacheOnWrite<Db>
where
    Db: Default,
{
    fn default() -> Self {
        Self::new(Db::default())
    }
}

impl<Db> CacheOnWrite<Db> {
    /// Create a new `CacheOnWrite` with the given inner database.
    pub fn new(inner: Db) -> Self {
        Self { cache: Default::default(), inner }
    }

    /// Create a new `CacheOnWrite` with the given inner database and cache.
    pub const fn new_with_cache(inner: Db, cache: Cache) -> Self {
        Self { cache, inner }
    }

    /// Get a reference to the inner database.
    pub const fn inner(&self) -> &Db {
        &self.inner
    }

    /// Get a mutable reference to the inner database.
    pub const fn inner_mut(&mut self) -> &mut Db {
        &mut self.inner
    }

    /// Get a refernce to the [`Cache`].
    pub const fn cache(&self) -> &Cache {
        &self.cache
    }

    /// Get a mutable reference to the [`Cache`].
    pub const fn cache_mut(&mut self) -> &mut Cache {
        &mut self.cache
    }

    /// Deconstruct the `CacheOnWrite` into its parts.
    pub fn into_parts(self) -> (Db, Cache) {
        (self.inner, self.cache)
    }

    /// Deconstruct the `CacheOnWrite` into its cache, dropping the `Db`.
    pub fn into_cache(self) -> Cache {
        self.cache
    }

    /// Nest the `CacheOnWrite` into a double cache.
    pub fn nest(self) -> CacheOnWrite<Self> {
        CacheOnWrite::new(self)
    }

    /// Inserts the account's code into the cache.
    ///
    /// Accounts objects and code are stored separately in the cache, this will take the code from the account and instead map it to the code hash.
    ///
    /// Note: This will not insert into the underlying external database.
    fn insert_contract(&mut self, account: &mut AccountInfo) {
        // Reproduced from
        // revm/crates/database/src/in_memory_db.rs
        if let Some(code) = &account.code {
            if !code.is_empty() {
                if account.code_hash == KECCAK_EMPTY {
                    account.code_hash = code.hash_slow();
                }
                self.cache.contracts.entry(account.code_hash).or_insert_with(|| code.clone());
            }
        }
        if account.code_hash.is_zero() {
            account.code_hash = KECCAK_EMPTY;
        }
    }
}

impl<Db> CachingDb for CacheOnWrite<Db> {
    fn cache(&self) -> &Cache {
        &self.cache
    }

    fn cache_mut(&mut self) -> &mut Cache {
        &mut self.cache
    }

    fn into_cache(self) -> Cache {
        self.cache
    }
}

impl<Db> CacheOnWrite<Db>
where
    Db: CachingDb,
{
    /// Flattens a nested cache by applying the outer cache to the inner cache.
    ///
    /// The behavior is as follows:
    /// - Accounts are overridden with outer accounts
    /// - Contracts are overridden with outer contracts
    /// - Block hashes are overridden with outer block hashes
    pub fn flatten(self) -> Db {
        let Self { cache, mut inner } = self;

        inner.extend(cache);
        inner
    }
}

impl<Db> CacheOnWrite<Db>
where
    Db: TryCachingDb,
{
    /// Attempts to flatten a nested cache by applying the outer cache to the
    /// inner cache. This is a fallible version of [`CacheOnWrite::flatten`].
    ///
    /// The behavior is as follows:
    /// - Accounts are overridden with outer accounts
    /// - Contracts are overridden with outer contracts
    /// - Block hashes are overridden with outer block hashes
    pub fn try_flatten(self) -> Result<Db, Db::Error> {
        let Self { cache, mut inner } = self;

        inner.try_extend(cache)?;
        Ok(inner)
    }
}

impl<Db: DatabaseRef> Database for CacheOnWrite<Db> {
    type Error = Db::Error;

    fn basic(&mut self, address: Address) -> Result<Option<AccountInfo>, Self::Error> {
        if let Some(account) = self.cache.accounts.get(&address).map(DbAccount::info) {
            return Ok(account);
        }
        self.inner.basic_ref(address)
    }

    fn code_by_hash(&mut self, code_hash: B256) -> Result<Bytecode, Self::Error> {
        Self::code_by_hash_ref(self, code_hash)
    }

    fn storage(&mut self, address: Address, index: U256) -> Result<U256, Self::Error> {
        Self::storage_ref(self, address, index)
    }

    fn block_hash(&mut self, number: u64) -> Result<B256, Self::Error> {
        Self::block_hash_ref(self, number)
    }
}

impl<Db: DatabaseRef> DatabaseRef for CacheOnWrite<Db> {
    type Error = Db::Error;

    fn basic_ref(&self, address: Address) -> Result<Option<AccountInfo>, Self::Error> {
        if let Some(account) = self.cache.accounts.get(&address).map(DbAccount::info) {
            return Ok(account);
        }
        self.inner.basic_ref(address)
    }

    fn code_by_hash_ref(&self, code_hash: B256) -> Result<Bytecode, Self::Error> {
        if let Some(code) = self.cache.contracts.get(&code_hash) {
            return Ok(code.clone());
        }
        self.inner.code_by_hash_ref(code_hash)
    }

    fn storage_ref(&self, address: Address, index: U256) -> Result<U256, Self::Error> {
        // Check if account exists in cache, and the storage state is occupied
        // in the cache
        if let Some(storage) =
            self.cache.accounts.get(&address).and_then(|a| a.storage.get(&index).cloned())
        {
            return Ok(storage);
        }
        // Cache miss (no account) or partial cache miss (no storage slot) - query inner DB
        self.inner.storage_ref(address, index)
    }

    fn block_hash_ref(&self, number: u64) -> Result<B256, Self::Error> {
        if let Some(hash) = self.cache.block_hashes.get(&U256::from(number)) {
            return Ok(*hash);
        }
        self.inner.block_hash_ref(number)
    }
}

impl<Db> DatabaseCommit for CacheOnWrite<Db> {
    fn commit(&mut self, changes: HashMap<Address, Account>) {
        // Reproduced from
        // revm/crates/database/src/in_memory_db.rs
        for (address, mut account) in changes {
            if !account.is_touched() {
                continue;
            }

            if account.is_selfdestructed() {
                let db_account = self.cache.accounts.entry(address).or_default();
                db_account.storage.clear();
                db_account.account_state = AccountState::NotExisting;
                db_account.info = AccountInfo::default();
                continue;
            }

            let is_newly_created = account.is_created();
            self.insert_contract(&mut account.info);

            let db_account = self.cache.accounts.entry(address).or_default();
            db_account.info = account.info;

            db_account.account_state = if is_newly_created {
                db_account.storage.clear();
                AccountState::StorageCleared
            } else if db_account.account_state.is_storage_cleared() {
                // Preserve old account state if it already exists
                AccountState::StorageCleared
            } else {
                AccountState::Touched
            };

            db_account.storage.extend(
                account.storage.into_iter().map(|(key, value)| (key, value.present_value())),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use revm::{
        database::InMemoryDB,
        state::{AccountStatus, EvmStorageSlot},
    };

    #[test]
    fn state_isolation_regression() {
        let mut mem_db = InMemoryDB::default();

        let address = Address::with_last_byte(42);

        // Write an account with storage at index 0 to the underlying DB
        let account = Account {
            info: AccountInfo { balance: U256::from(5000), ..Default::default() },
            storage: [(U256::from(0), EvmStorageSlot::new_changed(U256::ZERO, U256::from(42), 0))]
                .into_iter()
                .collect(),
            transaction_id: 0,
            status: AccountStatus::Touched,
        };

        let mut changes: std::collections::HashMap<
            Address,
            Account,
            revm::primitives::map::DefaultHashBuilder,
        > = Default::default();
        changes.insert(address, account);
        mem_db.commit(changes);

        // Read the items at index 1 and index 0 from the COW DB
        assert_eq!(mem_db.storage(address, U256::from(0)).unwrap(), U256::from(42));
        assert_eq!(mem_db.storage(address, U256::from(1)).unwrap(), U256::ZERO);

        // Stand up the COW DB on top of the underlying DB
        let mut cow_db = CacheOnWrite::new(mem_db);

        // Read the items at index 1 and index 0 from the COW DB
        assert_eq!(cow_db.storage(address, U256::from(0)).unwrap(), U256::from(42));
        assert_eq!(cow_db.storage(address, U256::from(1)).unwrap(), U256::ZERO);

        // Write a storage item at index 1 to the COW DB
        let account = Account {
            info: AccountInfo { balance: U256::from(5000), ..Default::default() },
            storage: [(U256::from(1), EvmStorageSlot::new_changed(U256::ZERO, U256::from(42), 0))]
                .into_iter()
                .collect(),
            transaction_id: 0,
            status: AccountStatus::Touched,
        };

        let mut changes: std::collections::HashMap<
            Address,
            Account,
            revm::primitives::map::DefaultHashBuilder,
        > = Default::default();
        changes.insert(address, account);
        cow_db.commit(changes);

        // Read the items at index 1 and index 0 from the COW DB
        assert_eq!(cow_db.storage(address, U256::from(0)).unwrap(), U256::from(42));
        assert_eq!(cow_db.storage(address, U256::from(1)).unwrap(), U256::from(42));
    }
}

// Some code above and documentation is adapted from the revm crate, and is
// reproduced here under the terms of the MIT license.
//
// MIT License
//
// Copyright (c) 2021-2024 draganrakita
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
