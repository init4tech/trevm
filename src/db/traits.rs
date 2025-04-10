use revm::{
    database::{states::bundle_state::BundleRetention, BundleState, Cache, CacheDB, State},
    primitives::B256,
    Database,
};
use std::{collections::BTreeMap, convert::Infallible, sync::Arc};

/// Abstraction trait covering types that accumulate state changes into a
/// [`BundleState`]. The prime example of this is [`State`]. These types are
/// use to accumulate state changes during the execution of a sequence of
/// transactions, and then provide access to the net changes in the form of a
/// [`BundleState`].
pub trait StateAcc {
    /// Set the state clear flag. See [`State::set_state_clear_flag`].
    fn set_state_clear_flag(&mut self, flag: bool);

    /// Merge transitions into the bundle. See [`State::merge_transitions`].
    fn merge_transitions(&mut self, retention: BundleRetention);

    /// Take the bundle. See [`State::take_bundle`].
    fn take_bundle(&mut self) -> BundleState;

    /// Set the block hashes, overriding any existing values, and inserting any
    /// absent values.
    fn set_block_hashes(&mut self, block_hashes: &BTreeMap<u64, B256>);
}

impl<Db: Database> StateAcc for State<Db> {
    fn set_state_clear_flag(&mut self, flag: bool) {
        Self::set_state_clear_flag(self, flag)
    }

    fn merge_transitions(&mut self, retention: BundleRetention) {
        Self::merge_transitions(self, retention)
    }

    fn take_bundle(&mut self) -> BundleState {
        Self::take_bundle(self)
    }

    fn set_block_hashes(&mut self, block_hashes: &BTreeMap<u64, B256>) {
        self.block_hashes.extend(block_hashes)
    }
}

/// Fallible version of [`StateAcc`].
///
/// Abstraction trait covering types that accumulate state changes into a
/// [`BundleState`]. The prime example of this is [`State`]. These types are
/// use to accumulate state changes during the execution of a sequence of
/// transactions, and then provide access to the net changes in the form of a
/// [`BundleState`].
///
/// The primary motivator for this trait is to allow for the implementation of
/// [`StateAcc`] for [`Arc`]-wrapped DBs, which may fail to mutate if the
/// reference is not unique.
pub trait TryStateAcc: Sync {
    /// Error type to be thrown when state accumulation fails.
    type Error: core::error::Error;

    /// Attempt to set the state clear flag. See [`State::set_state_clear_flag`].
    fn try_set_state_clear_flag(&mut self, flag: bool) -> Result<(), Self::Error>;

    /// Attempt to merge transitions into the bundle. See
    /// [`State::merge_transitions`].
    fn try_merge_transitions(&mut self, retention: BundleRetention) -> Result<(), Self::Error>;

    /// Attempt to take the bundle. See [`State::take_bundle`].
    fn try_take_bundle(&mut self) -> Result<BundleState, Self::Error>;

    /// Attempt to set the block hashes, overriding any existing values, and
    /// inserting any absent values.
    fn try_set_block_hashes(
        &mut self,
        block_hashes: &BTreeMap<u64, B256>,
    ) -> Result<(), Self::Error>;
}

impl<Db> TryStateAcc for Db
where
    Db: StateAcc + Sync,
{
    type Error = Infallible;

    fn try_set_state_clear_flag(&mut self, flag: bool) -> Result<(), Infallible> {
        self.set_state_clear_flag(flag);
        Ok(())
    }

    fn try_merge_transitions(&mut self, retention: BundleRetention) -> Result<(), Infallible> {
        self.merge_transitions(retention);
        Ok(())
    }

    fn try_take_bundle(&mut self) -> Result<BundleState, Infallible> {
        Ok(self.take_bundle())
    }

    fn try_set_block_hashes(
        &mut self,
        block_hashes: &BTreeMap<u64, B256>,
    ) -> Result<(), Infallible> {
        self.set_block_hashes(block_hashes);
        Ok(())
    }
}

/// Error type for implementation of [`TryStateAcc`] for [`Arc`]-wrapped
/// DBs.
#[derive(thiserror::Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArcUpgradeError {
    /// Arc reference is not unique. Ensure that all other references are
    /// dropped before attempting to mutate the state.
    #[error("Arc reference is not unique, cannot mutate")]
    NotUnique,
}

impl<Db> TryStateAcc for Arc<Db>
where
    Db: StateAcc + Sync + Send,
{
    type Error = ArcUpgradeError;

    fn try_set_state_clear_flag(&mut self, flag: bool) -> Result<(), ArcUpgradeError> {
        Self::get_mut(self).ok_or(ArcUpgradeError::NotUnique)?.set_state_clear_flag(flag);
        Ok(())
    }

    fn try_merge_transitions(&mut self, retention: BundleRetention) -> Result<(), ArcUpgradeError> {
        Self::get_mut(self).ok_or(ArcUpgradeError::NotUnique)?.merge_transitions(retention);
        Ok(())
    }

    fn try_take_bundle(&mut self) -> Result<BundleState, ArcUpgradeError> {
        Ok(Self::get_mut(self).ok_or(ArcUpgradeError::NotUnique)?.take_bundle())
    }

    fn try_set_block_hashes(
        &mut self,
        block_hashes: &BTreeMap<u64, B256>,
    ) -> Result<(), ArcUpgradeError> {
        Self::get_mut(self).ok_or(ArcUpgradeError::NotUnique)?.set_block_hashes(block_hashes);
        Ok(())
    }
}

/// Trait for Databases that have a [`Cache`].
pub trait CachingDb {
    /// Get the cache.
    fn cache(&self) -> &Cache;

    /// Get the cache mutably.
    fn cache_mut(&mut self) -> &mut Cache;

    /// Deconstruct into the cache
    fn into_cache(self) -> Cache;

    /// Extend the cache with the given cache by copying data.
    ///
    /// The behavior is as follows:
    /// - Accounts are overridden with outer accounts
    /// - Contracts are overridden with outer contracts
    /// - Logs are appended
    /// - Block hashes are overridden with outer block hashes
    fn extend_ref(&mut self, cache: &Cache) {
        self.cache_mut().accounts.extend(cache.accounts.iter().map(|(k, v)| (*k, v.clone())));
        self.cache_mut().contracts.extend(cache.contracts.iter().map(|(k, v)| (*k, v.clone())));
        self.cache_mut().logs.extend(cache.logs.iter().cloned());
        self.cache_mut()
            .block_hashes
            .extend(cache.block_hashes.iter().map(|(k, v)| (*k, *v)));
    }

    /// Extend the cache with the given cache by moving data.
    ///
    /// The behavior is as follows:
    /// - Accounts are overridden with outer accounts
    /// - Contracts are overridden with outer contracts
    /// - Logs are appended
    /// - Block hashes are overridden with outer block hashes
    fn extend(&mut self, cache: Cache) {
        self.cache_mut().accounts.extend(cache.accounts);
        self.cache_mut().contracts.extend(cache.contracts);
        self.cache_mut().logs.extend(cache.logs);
        self.cache_mut().block_hashes.extend(cache.block_hashes);
    }
}

impl<Db> CachingDb for CacheDB<Db> {
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

/// Trait for Databases that have a [`Cache`] and can fail to mutably access
/// it. E.g. `Arc<CacheDB<Db>>`
pub trait TryCachingDb {
    /// Error type to be thrown when cache access fails.
    type Error: core::error::Error;

    /// Attempt to get the cache.
    fn cache(&self) -> &Cache;

    /// Attempt to get the cache mutably.
    fn try_cache_mut(&mut self) -> Result<&mut Cache, Self::Error>;

    /// Attempt to deconstruct into the cache
    fn try_into_cache(self) -> Result<Cache, Self::Error>;

    /// Attempt to fold a cache into the database.
    ///
    /// The behavior is as follows:
    /// - Accounts are overridden with outer accounts
    /// - Contracts are overridden with outer contracts
    /// - Logs are appended
    /// - Block hashes are overridden with outer block hashes
    fn try_extend_ref(&mut self, cache: &Cache) -> Result<(), Self::Error>
    where
        Self: Sized,
    {
        let inner_cache = self.try_cache_mut()?;
        inner_cache.accounts.extend(cache.accounts.iter().map(|(k, v)| (*k, v.clone())));
        inner_cache.contracts.extend(cache.contracts.iter().map(|(k, v)| (*k, v.clone())));
        inner_cache.logs.extend(cache.logs.iter().cloned());
        inner_cache.block_hashes.extend(cache.block_hashes.iter().map(|(k, v)| (*k, *v)));
        Ok(())
    }

    /// Attempt to extend the cache with the given cache by moving data.
    ///
    /// The behavior is as follows:
    /// - Accounts are overridden with outer accounts
    /// - Contracts are overridden with outer contracts
    /// - Logs are appended
    /// - Block hashes are overridden with outer block hashes
    fn try_extend(&mut self, cache: Cache) -> Result<(), Self::Error>
    where
        Self: Sized,
    {
        let inner_cache = self.try_cache_mut()?;
        inner_cache.accounts.extend(cache.accounts);
        inner_cache.contracts.extend(cache.contracts);
        inner_cache.logs.extend(cache.logs);
        inner_cache.block_hashes.extend(cache.block_hashes);
        Ok(())
    }
}

impl<Db> TryCachingDb for Arc<Db>
where
    Db: CachingDb,
{
    type Error = ArcUpgradeError;

    fn cache(&self) -> &Cache {
        self.as_ref().cache()
    }

    fn try_cache_mut(&mut self) -> Result<&mut Cache, Self::Error> {
        Self::get_mut(self).ok_or(ArcUpgradeError::NotUnique).map(|db| db.cache_mut())
    }

    fn try_into_cache(self) -> Result<Cache, Self::Error> {
        Self::into_inner(self).ok_or(ArcUpgradeError::NotUnique).map(|db| db.into_cache())
    }
}
