mod builder;

pub use builder::ConcurrentStateBuilder;

mod cache;
pub use cache::ConcurrentCacheState;

mod state;
pub use state::{ConcurrentState, ConcurrentStateInfo};

use crate::db::StateAcc;
use revm::{
    db::{states::bundle_state::BundleRetention, BundleState},
    primitives::B256,
    DatabaseRef,
};
use std::collections::BTreeMap;

impl<Db: DatabaseRef + Sync> StateAcc for ConcurrentState<Db> {
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
        self.info.block_hashes.write().unwrap().extend(block_hashes)
    }
}
