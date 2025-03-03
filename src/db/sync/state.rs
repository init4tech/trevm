use crate::db::sync::{ConcurrentCacheState, ConcurrentStateError};
use alloy::primitives::{Address, B256, U256};
use dashmap::mapref::one::RefMut;
use revm::{
    db::{
        states::{bundle_state::BundleRetention, plain_account::PlainStorage, CacheAccount},
        BundleState, State,
    },
    primitives::{Account, AccountInfo, Bytecode},
    Database, DatabaseCommit, DatabaseRef, TransitionAccount, TransitionState,
};
use std::{
    collections::{hash_map, BTreeMap},
    sync::{Arc, RwLock},
};

/// A [`Child`] is a [`CacheDB`] that wraps a [`ConcurrentState`].
pub type Child<Db> = ConcurrentState<Arc<ConcurrentState<Db>>>;

/// State of the blockchain.
///
/// A version of [`revm::db::State`] that can be shared between threads.
#[derive(Debug)]
pub struct ConcurrentState<Db> {
    database: Db,
    /// Non-DB state cache and transition information.
    pub info: ConcurrentStateInfo,
}

impl<Db> From<State<Db>> for ConcurrentState<Db>
where
    Db: DatabaseRef,
{
    fn from(value: State<Db>) -> Self {
        Self {
            database: value.database,
            info: ConcurrentStateInfo {
                cache: value.cache.into(),
                transition_state: value.transition_state,
                bundle_state: value.bundle_state,
                use_preloaded_bundle: value.use_preloaded_bundle,
                block_hashes: value.block_hashes.into(),
            },
        }
    }
}

impl<Db> ConcurrentState<Db> {
    /// Deconstruct the [`ConcurrentState`] into its parts.
    pub fn into_parts(self) -> (Db, ConcurrentStateInfo) {
        (self.database, self.info)
    }

    /// Returns the size hint for the inner bundle state.
    /// See [BundleState::size_hint] for more info.
    pub fn bundle_size_hint(&self) -> usize {
        self.info.bundle_state.size_hint()
    }

    /// State clear EIP-161 is enabled in Spurious Dragon hardfork.
    pub fn set_state_clear_flag(&mut self, has_state_clear: bool) {
        self.info.cache.set_state_clear_flag(has_state_clear);
    }

    /// Insert not existing account into cache state.
    pub fn insert_not_existing(&mut self, address: Address) {
        self.info.cache.insert_not_existing(address)
    }

    /// Insert account into cache state.
    pub fn insert_account(&mut self, address: Address, info: AccountInfo) {
        self.info.cache.insert_account(address, info)
    }

    /// Insert account with storage into cache state.
    pub fn insert_account_with_storage(
        &mut self,
        address: Address,
        info: AccountInfo,
        storage: PlainStorage,
    ) {
        self.info.cache.insert_account_with_storage(address, info, storage)
    }

    /// Apply evm transitions to transition state.
    pub fn apply_transition(&mut self, transitions: Vec<(Address, TransitionAccount)>) {
        // add transition to transition state.
        if let Some(s) = self.info.transition_state.as_mut() {
            s.add_transitions(transitions)
        }
    }

    /// Take all transitions and merge them inside bundle state.
    /// This action will create final post state and all reverts so that
    /// we at any time revert state of bundle to the state before transition
    /// is applied.
    pub fn merge_transitions(&mut self, retention: BundleRetention) {
        if let Some(transition_state) = self.info.transition_state.take() {
            self.info
                .bundle_state
                .apply_transitions_and_create_reverts(transition_state, retention);
        }
    }

    // TODO make cache aware of transitions dropping by having global transition counter.
    /// Takes the [`BundleState`] changeset from the [`ConcurrentState`],
    /// replacing it
    /// with an empty one.
    ///
    /// This will not apply any pending [`TransitionState`]. It is recommended
    /// to call [`ConcurrentState::merge_transitions`] before taking the bundle.
    ///
    /// If the `State` has been built with the
    /// [`revm::StateBuilder::with_bundle_prestate`] option, the pre-state will be
    /// taken along with any changes made by
    /// [`ConcurrentState::merge_transitions`].
    pub fn take_bundle(&mut self) -> BundleState {
        core::mem::take(&mut self.info.bundle_state)
    }
}

impl<Db: DatabaseRef + Sync> ConcurrentState<Db> {
    /// Create a new [`ConcurrentState`] with the given database and cache
    /// state.
    pub const fn new(database: Db, info: ConcurrentStateInfo) -> Self {
        Self { database, info }
    }

    /// Iterate over received balances and increment all account balances.
    /// If account is not found inside cache state it will be loaded from database.
    ///
    /// Update will create transitions for all accounts that are updated.
    ///
    /// Like [`CacheAccount::increment_balance`], this assumes that incremented balances are not
    /// zero, and will not overflow once incremented. If using this to implement withdrawals, zero
    /// balances must be filtered out before calling this function.
    pub fn increment_balances(
        &mut self,
        balances: impl IntoIterator<Item = (Address, u128)>,
    ) -> Result<(), Db::Error> {
        // make transition and update cache state
        let mut transitions = Vec::new();
        for (address, balance) in balances {
            if balance == 0 {
                continue;
            }
            let mut original_account = self.load_cache_account_mut(address)?;
            transitions.push((
                address,
                original_account.increment_balance(balance).expect("Balance is not zero"),
            ))
        }
        // append transition
        if let Some(s) = self.info.transition_state.as_mut() {
            s.add_transitions(transitions)
        }
        Ok(())
    }

    /// Drain balances from given account and return those values.
    ///
    /// It is used for DAO hardfork state change to move values from given accounts.
    pub fn drain_balances(
        &mut self,
        addresses: impl IntoIterator<Item = Address>,
    ) -> Result<Vec<u128>, Db::Error> {
        // make transition and update cache state
        let mut transitions = Vec::new();
        let mut balances = Vec::new();
        for address in addresses {
            let mut original_account = self.load_cache_account_mut(address)?;
            let (balance, transition) = original_account.drain_balance();
            balances.push(balance);
            transitions.push((address, transition))
        }
        // append transition
        if let Some(s) = self.info.transition_state.as_mut() {
            s.add_transitions(transitions)
        }
        Ok(balances)
    }

    /// Get a mutable reference to the [`CacheAccount`] for the given address.
    /// If the account is not found in the cache, it will be loaded from the
    /// database and inserted into the cache.
    ///
    /// This function locks that account in the cache while the reference is
    /// held. For that timeframe, it will block other tasks attempting to
    /// access that account. As a result, this function should be used
    /// sparingly.
    pub fn load_cache_account_mut(
        &self,
        address: Address,
    ) -> Result<RefMut<'_, Address, CacheAccount>, Db::Error> {
        match self.info.cache.accounts.entry(address) {
            dashmap::Entry::Vacant(entry) => {
                if self.info.use_preloaded_bundle {
                    // load account from bundle state
                    if let Some(account) =
                        self.info.bundle_state.account(&address).cloned().map(Into::into)
                    {
                        return Ok(entry.insert(account));
                    }
                }
                // if not found in bundle, load it from database
                let info = self.database.basic_ref(address)?;
                let account = match info {
                    None => CacheAccount::new_loaded_not_existing(),
                    Some(acc) if acc.is_empty() => {
                        CacheAccount::new_loaded_empty_eip161(PlainStorage::default())
                    }
                    Some(acc) => CacheAccount::new_loaded(acc, PlainStorage::default()),
                };
                Ok(entry.insert(account))
            }
            dashmap::Entry::Occupied(entry) => Ok(entry.into_ref()),
        }
    }

    /// Create a [`Child`] DB that wraps this state in another cache layer.
    ///
    /// This allows the [`ConcurrentState`] to be shared between threads, with
    /// each thread having a separate cache for its local changes. The child
    /// can later be merged back into the parent with [`Self::merge_child`] IF
    /// no other children or copies of the `Arc<Self>` exist.
    pub fn child(self: &Arc<Self>) -> Child<Db>
    where
        Db: Send,
    {
        ConcurrentState::new(self.clone(), Default::default())
    }

    /// Merge a child DB into this DB, incorporating its changes and overwriting
    /// any present values. If other children or other copies of the
    /// `Arc<Self>` exist, this will fail with a [`ArcUpgradeError::NotUnique`]
    /// error.
    ///
    /// This function needs to take ownership of the child to ensure that the
    pub fn merge_child(self: &mut Arc<Self>, child: Child<Db>) -> Result<(), ConcurrentStateError> {
        self.can_merge(&child)?;

        let (_, info) = child.into_parts();

        let this = Arc::get_mut(self).ok_or_else(ConcurrentStateError::not_unique)?;

        this.info.cache.absorb(info.cache);
        Ok(())
    }

    /// True if the child can be merged into this state, false otherwise.
    ///
    /// ## Note
    ///
    /// Race conditions can occur if the child is shared between threads, as
    /// the child may be cloned AFTER this check is made, but BEFORE the child
    /// is merged. In this case the function will spuriously return `Ok(())`
    /// even though the merge will fail. To avoid this, ensure that the child
    /// is not shared between threads when [`Self::can_merge`] is called.
    pub fn can_merge(self: &Arc<Self>, child: &Child<Db>) -> Result<(), ConcurrentStateError> {
        if !self.is_parent(child) {
            return Err(ConcurrentStateError::not_parent());
        }

        if Arc::strong_count(self) != 2 {
            return Err(ConcurrentStateError::not_unique());
        }

        Ok(())
    }

    /// True if the child is a child of this state, false otherwise.
    pub fn is_parent(self: &Arc<Self>, child: &Child<Db>) -> bool {
        Arc::ptr_eq(self, &child.database)
    }
}

impl<Db: DatabaseRef + Sync> DatabaseRef for ConcurrentState<Db> {
    type Error = Db::Error;

    fn basic_ref(&self, address: Address) -> Result<Option<AccountInfo>, Self::Error> {
        self.load_cache_account_mut(address).map(|a| a.account_info())
    }

    fn code_by_hash_ref(&self, code_hash: B256) -> Result<Bytecode, Self::Error> {
        let res = match self.info.cache.contracts.entry(code_hash) {
            dashmap::Entry::Occupied(entry) => Ok(entry.get().clone()),
            dashmap::Entry::Vacant(entry) => {
                if self.info.use_preloaded_bundle {
                    if let Some(code) = self.info.bundle_state.contracts.get(&code_hash) {
                        entry.insert(code.clone());
                        return Ok(code.clone());
                    }
                }
                // if not found in bundle ask database
                let code = self.database.code_by_hash_ref(code_hash)?;
                entry.insert(code.clone());
                Ok(code)
            }
        };
        res
    }

    fn storage_ref(&self, address: Address, index: U256) -> Result<U256, Self::Error> {
        // Account is guaranteed to be loaded.
        // Note that storage from bundle is already loaded with account.
        if let Some(mut account) = self.info.cache.accounts.get_mut(&address) {
            // account will always be some, but if it is not, U256::ZERO will be returned.
            let is_storage_known = account.status.is_storage_known();
            Ok(account
                .account
                .as_mut()
                .map(|account| match account.storage.entry(index) {
                    hash_map::Entry::Occupied(entry) => Ok(*entry.get()),
                    hash_map::Entry::Vacant(entry) => {
                        // if account was destroyed or account is newly built
                        // we return zero and don't ask database.
                        let value = if is_storage_known {
                            U256::ZERO
                        } else {
                            self.database.storage_ref(address, index)?
                        };
                        entry.insert(value);
                        Ok(value)
                    }
                })
                .transpose()?
                .unwrap_or_default())
        } else {
            unreachable!("For accessing any storage account is guaranteed to be loaded beforehand")
        }
    }

    fn block_hash_ref(&self, number: u64) -> Result<B256, Self::Error> {
        {
            let hashes = self.info.block_hashes.read().unwrap();
            if let Some(hash) = hashes.get(&number) {
                return Ok(*hash);
            }
        }

        let hash = self.database.block_hash_ref(number)?;

        let mut hashes = self.info.block_hashes.write().unwrap();

        hashes.insert(number, hash);

        // prune all hashes that are older then BLOCK_HASH_HISTORY
        let last_block = number.saturating_sub(revm::primitives::BLOCK_HASH_HISTORY);

        // lock the hashes, split at the key, and retain the newer hashes
        let mut hashes = self.info.block_hashes.write().unwrap();
        let to_retain = hashes.split_off(&last_block);
        *hashes = to_retain;

        Ok(hash)
    }
}

impl<Db: DatabaseRef + Sync> DatabaseCommit for ConcurrentState<Db> {
    fn commit(&mut self, evm_state: revm::primitives::HashMap<Address, Account>) {
        let transitions = self.info.cache.apply_evm_state(evm_state);
        self.apply_transition(transitions);
    }
}

impl<Db: DatabaseRef + Sync> Database for ConcurrentState<Db> {
    type Error = <Self as DatabaseRef>::Error;

    fn basic(&mut self, address: Address) -> Result<Option<AccountInfo>, Self::Error> {
        self.basic_ref(address)
    }

    fn code_by_hash(&mut self, code_hash: B256) -> Result<Bytecode, Self::Error> {
        self.code_by_hash_ref(code_hash)
    }

    fn storage(&mut self, address: Address, index: U256) -> Result<U256, Self::Error> {
        self.storage_ref(address, index)
    }

    fn block_hash(&mut self, number: u64) -> Result<B256, Self::Error> {
        self.block_hash_ref(number)
    }
}

/// Non-DB contents of [`ConcurrentState`]
#[derive(Debug, Default)]
pub struct ConcurrentStateInfo {
    /// Cached state contains both changed from evm execution and cached/loaded
    /// account/storages from database. This allows us to have only one layer
    /// of cache where we can fetch data. Additionally we can introduce some
    /// preloading of data from database.
    pub cache: ConcurrentCacheState,
    /// Block state, it aggregates transactions transitions into one state.
    ///
    /// Build reverts and state that gets applied to the state.
    pub transition_state: Option<TransitionState>,
    /// After block is finishes we merge those changes inside bundle.
    /// Bundle is used to update database and create changesets.
    /// Bundle state can be set on initialization if we want to use preloaded
    /// bundle.
    pub bundle_state: BundleState,
    /// Addition layer that is going to be used to fetched values before
    /// fetching values from database.
    ///
    /// Bundle is the main output of the state execution and this allows
    /// setting previous bundle and using its values for execution.
    pub use_preloaded_bundle: bool,
    /// If EVM asks for block hash we will first check if they are found here.
    /// and then ask the database.
    ///
    /// This map can be used to give different values for block hashes if in
    /// case the fork block is different or some blocks are not saved inside
    /// database.
    pub block_hashes: RwLock<BTreeMap<u64, B256>>,
}

#[cfg(test)]
mod test {
    use super::*;
    use revm::db::EmptyDB;

    #[test]
    fn assert_child_trait_impls() {
        fn assert_database_ref<T: DatabaseRef>() {}
        fn assert_database_commit<T: DatabaseCommit>() {}
        fn assert_database<T: Database>() {}

        assert_database_ref::<Child<EmptyDB>>();
        assert_database_commit::<Child<EmptyDB>>();
        assert_database::<Child<EmptyDB>>();
    }

    #[test]
    fn merge_child() {
        let addr = Address::repeat_byte(1);

        let mut parent = Arc::new(ConcurrentState::new(EmptyDB::new(), Default::default()));
        let mut child = parent.child();

        child.increment_balances([(addr, 100)].into_iter()).unwrap();

        // Check that the parent is not modified
        assert!(parent.load_cache_account_mut(addr).unwrap().value().account_info().is_none());
        assert_eq!(
            child.load_cache_account_mut(addr).unwrap().value().account_info().unwrap().balance,
            U256::from(100)
        );
        assert_eq!(Arc::strong_count(&parent), 2);

        // Check that it errors if there are 2 kids
        let child_2 = parent.child();
        assert_eq!(parent.merge_child(child_2).unwrap_err(), ConcurrentStateError::not_unique());

        // Check that it won't absorb the child of a different parent
        let parent_2 = Arc::new(ConcurrentState::new(EmptyDB::new(), Default::default()));
        let child_2 = parent_2.child();
        assert_eq!(parent.merge_child(child_2).unwrap_err(), ConcurrentStateError::not_parent());

        // now merge
        parent.merge_child(child).unwrap();

        // Check that the child is now merged
        assert_eq!(
            parent.load_cache_account_mut(addr).unwrap().value().account_info().unwrap().balance,
            U256::from(100)
        );
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
