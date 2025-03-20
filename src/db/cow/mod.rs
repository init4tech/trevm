use alloy::{
    consensus::constants::KECCAK_EMPTY,
    primitives::{Address, B256, U256},
};
use revm::{
    db::{AccountState, DbAccount},
    primitives::{Account, AccountInfo, Bytecode, HashMap},
    Database, DatabaseCommit, DatabaseRef,
};

/// Cache for [`CacheOnWrite`].
#[derive(Debug, Default, Clone)]
pub struct Cache {
    accounts: HashMap<Address, DbAccount>,
    contracts: HashMap<B256, Bytecode>,
    block_hashes: HashMap<U256, B256>,
}

impl Cache {
    /// Inserts the account's code into the cache.
    ///
    /// Accounts objects and code are stored separately in the cache, this will take the code from the account and instead map it to the code hash.
    ///
    /// Note: This will not insert into the underlying external database.
    fn insert_contract(&mut self, account: &mut AccountInfo) {
        if let Some(code) = &account.code {
            if !code.is_empty() {
                if account.code_hash == KECCAK_EMPTY {
                    account.code_hash = code.hash_slow();
                }
                self.contracts.entry(account.code_hash).or_insert_with(|| code.clone());
            }
        }

        if account.code_hash.is_zero() {
            account.code_hash = KECCAK_EMPTY;
        }
    }

    /// Absorb another cache into this cache, overwriting any existing entries
    fn absorb(&mut self, other: Cache) {
        self.accounts.extend(other.accounts);
        self.contracts.extend(other.contracts);
        self.block_hashes.extend(other.block_hashes);
    }
}

/// A version of [`CacheDB`] that caches only on write, not on read.
///
/// This saves memory when wrapping some other caching database, like [`State`]
/// or [`ConcurrentState`].
///
/// [`CacheDB`]: revm::db::in_memory_db::CacheDB
/// [`State`]: revm::db::State
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
    pub fn new_with_cache(inner: Db, cache: Cache) -> Self {
        Self { cache, inner }
    }

    /// Get a reference to the inner database.
    pub fn inner(&self) -> &Db {
        &self.inner
    }

    /// Get a refernce to the [`Cache`].
    pub fn cache(&self) -> &Cache {
        &self.cache
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
    pub fn nest(self) -> CacheOnWrite<CacheOnWrite<Db>> {
        CacheOnWrite::new(self)
    }
}

impl<Db> CacheOnWrite<CacheOnWrite<Db>> {
    /// Discard the outer cache, returning the inner.
    pub fn discard_outer(self) -> CacheOnWrite<Db> {
        self.inner
    }

    /// Flattens a nested cache by applying the outer cache to the inner cache.
    ///
    /// The behavior is as follows:
    /// - Accounts are overridden with outer accounts
    /// - Contracts are overridden with outer contracts
    /// - Block hashes are overridden with outer block hashes
    pub fn flatten(self) -> CacheOnWrite<Db> {
        let (mut this, outer) = self.into_parts();
        this.cache.absorb(outer);
        this
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
        if let Some(code) = self.cache.contracts.get(&code_hash) {
            return Ok(code.clone());
        }
        self.inner.code_by_hash_ref(code_hash)
    }

    fn storage(&mut self, address: Address, index: U256) -> Result<U256, Self::Error> {
        if let Some(storage) =
            self.cache.accounts.get(&address).map(|a| a.storage.get(&index).cloned())
        {
            return Ok(storage.unwrap_or_default());
        }
        self.inner.storage_ref(address, index)
    }

    fn block_hash(&mut self, number: u64) -> Result<B256, Self::Error> {
        if let Some(hash) = self.cache.block_hashes.get(&U256::from(number)) {
            return Ok(hash.clone());
        }
        self.inner.block_hash_ref(number)
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
        if let Some(storage) =
            self.cache.accounts.get(&address).map(|a| a.storage.get(&index).cloned())
        {
            return Ok(storage.unwrap_or_default());
        }
        self.inner.storage_ref(address, index)
    }

    fn block_hash_ref(&self, number: u64) -> Result<B256, Self::Error> {
        if let Some(hash) = self.cache.block_hashes.get(&U256::from(number)) {
            return Ok(hash.clone());
        }
        self.inner.block_hash_ref(number)
    }
}

impl<Db> DatabaseCommit for CacheOnWrite<Db> {
    fn commit(&mut self, changes: HashMap<Address, Account>) {
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
            self.cache.insert_contract(&mut account.info);

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
