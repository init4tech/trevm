use crate::db::ConcurrentState;
use revm::{
    db::{
        states::{BundleState, TransitionState},
        EmptyDB,
    },
    primitives::{db::DatabaseRef, B256},
};
use std::collections::BTreeMap;

use super::{ConcurrentCacheState, ConcurrentStateInfo};

/// Allows building of State and initializing it with different options.
#[derive(Clone, Debug)]
pub struct ConcurrentStateBuilder<Db> {
    /// Database that we use to fetch data from.
    database: Db,
    /// Enabled state clear flag that is introduced in Spurious Dragon hardfork.
    /// Default is true as spurious dragon happened long time ago.
    with_state_clear: bool,
    /// if there is prestate that we want to use.
    /// This would mean that we have additional state layer between evm and disk/database.
    with_bundle_prestate: Option<BundleState>,
    /// This will initialize cache to this state.
    with_cache_prestate: Option<ConcurrentCacheState>,
    /// Do we want to create reverts and update bundle state.
    /// Default is false.
    with_bundle_update: bool,
    /// Do we want to merge transitions in background.
    /// This will allows evm to continue executing.
    /// Default is false.
    with_background_transition_merge: bool,
    /// If we want to set different block hashes
    with_block_hashes: BTreeMap<u64, B256>,
}

impl ConcurrentStateBuilder<EmptyDB> {
    /// Create a new builder with an empty database.
    ///
    /// If you want to instantiate it with a specific database, use
    /// [`new_with_database`](Self::new_with_database).
    pub fn new() -> Self {
        Self::default()
    }
}

impl<Db: DatabaseRef + Sync + Default> Default for ConcurrentStateBuilder<Db> {
    fn default() -> Self {
        Self::new_with_database(Db::default())
    }
}

impl<Db: DatabaseRef + Sync> ConcurrentStateBuilder<Db> {
    /// Create a new builder with the given database.
    pub const fn new_with_database(database: Db) -> Self {
        Self {
            database,
            with_state_clear: true,
            with_cache_prestate: None,
            with_bundle_prestate: None,
            with_bundle_update: false,
            with_background_transition_merge: false,
            with_block_hashes: BTreeMap::new(),
        }
    }

    /// Set the database.
    pub fn with_database<ODb: DatabaseRef + Sync>(
        self,
        database: ODb,
    ) -> ConcurrentStateBuilder<ODb> {
        // cast to the different database,
        // Note that we return different type depending of the database NewDBError.
        ConcurrentStateBuilder {
            with_state_clear: self.with_state_clear,
            database,
            with_cache_prestate: self.with_cache_prestate,
            with_bundle_prestate: self.with_bundle_prestate,
            with_bundle_update: self.with_bundle_update,
            with_background_transition_merge: self.with_background_transition_merge,
            with_block_hashes: self.with_block_hashes,
        }
    }

    /// Alias for [`Self::with_database`], for revm compat reasons.
    pub fn with_database_ref<ODb: DatabaseRef + Sync>(
        self,
        database: ODb,
    ) -> ConcurrentStateBuilder<ODb> {
        self.with_database(database)
    }

    /// By default state clear flag is enabled but for initial sync on mainnet
    /// we want to disable it so proper consensus changes are in place.
    pub fn without_state_clear(self) -> Self {
        Self { with_state_clear: false, ..self }
    }

    /// Allows setting prestate that is going to be used for execution.
    /// This bundle state will act as additional layer of cache.
    /// and State after not finding data inside StateCache will try to find it inside BundleState.
    ///
    /// On update Bundle state will be changed and updated.
    pub fn with_bundle_prestate(self, bundle: BundleState) -> Self {
        Self { with_bundle_prestate: Some(bundle), ..self }
    }

    /// Make transitions and update bundle state.
    ///
    /// This is needed option if we want to create reverts
    /// and getting output of changed states.
    pub fn with_bundle_update(self) -> Self {
        Self { with_bundle_update: true, ..self }
    }

    /// It will use different cache for the state. If set, it will ignore bundle prestate.
    /// and will ignore `without_state_clear` flag as cache contains its own state_clear flag.
    ///
    /// This is useful for testing.
    pub fn with_cached_prestate(self, cache: impl Into<ConcurrentCacheState>) -> Self {
        Self { with_cache_prestate: Some(cache.into()), ..self }
    }

    /// Starts the thread that will take transitions and do merge to the bundle state
    /// in the background.
    pub fn with_background_transition_merge(self) -> Self {
        Self { with_background_transition_merge: true, ..self }
    }

    /// Add block hashes to the state.
    pub fn with_block_hashes(self, block_hashes: BTreeMap<u64, B256>) -> Self {
        Self { with_block_hashes: block_hashes, ..self }
    }

    /// Build the concurrent state.
    pub fn build(mut self) -> ConcurrentState<Db> {
        let use_preloaded_bundle = if self.with_cache_prestate.is_some() {
            self.with_bundle_prestate = None;
            false
        } else {
            self.with_bundle_prestate.is_some()
        };
        ConcurrentState::new(
            self.database,
            ConcurrentStateInfo {
                cache: self
                    .with_cache_prestate
                    .unwrap_or_else(|| ConcurrentCacheState::new(self.with_state_clear)),
                transition_state: self.with_bundle_update.then(TransitionState::default),
                bundle_state: self.with_bundle_prestate.unwrap_or_default(),
                use_preloaded_bundle,
                block_hashes: self.with_block_hashes.into(),
            },
        )
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
