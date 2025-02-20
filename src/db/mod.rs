mod builder;

use alloy::rpc::types::BlockOverrides;
pub use builder::ConcurrentStateBuilder;

mod cache_state;
pub use cache_state::ConcurrentCacheState;

mod sync_state;
pub use sync_state::{ConcurrentState, ConcurrentStateInfo};

use crate::{Block, EvmNeedsBlock, EvmNeedsTx, Trevm};
use revm::{
    db::{states::bundle_state::BundleRetention, BundleState},
    DatabaseRef,
};

impl<Ext, Db: DatabaseRef + Sync, TrevmState> Trevm<'_, Ext, ConcurrentState<Db>, TrevmState> {
    /// Set the [EIP-161] state clear flag, activated in the Spurious Dragon
    /// hardfork.
    ///
    /// This function changes the behavior of the inner [`ConcurrentState`].
    pub fn set_state_clear_flag(&mut self, flag: bool) {
        self.inner.db_mut().set_state_clear_flag(flag)
    }
}

impl<Ext, Db: DatabaseRef + Sync> EvmNeedsBlock<'_, Ext, ConcurrentState<Db>> {
    /// Finish execution and return the outputs.
    ///
    /// If the State has not been built with
    /// [revm::StateBuilder::with_bundle_update] then the returned
    /// [`BundleState`] will be meaningless.
    ///
    /// See [`ConcurrentState::merge_transitions`] and
    /// [`ConcurrentState::take_bundle`].
    pub fn finish(self) -> BundleState {
        let Self { inner: mut evm, .. } = self;
        evm.db_mut().merge_transitions(BundleRetention::Reverts);
        let bundle = evm.db_mut().take_bundle();

        bundle
    }
}

impl<Ext, Db: DatabaseRef + Sync> EvmNeedsTx<'_, Ext, ConcurrentState<Db>> {
    /// Apply block overrides to the current block.
    ///
    /// Note that this is NOT reversible. The overrides are applied directly to
    /// the underlying state and these changes cannot be removed. If it is
    /// important that you have access to the pre-change state, you should wrap
    /// the existing DB in a new [`State`] and apply the overrides to that.
    pub fn apply_block_overrides(mut self, overrides: &BlockOverrides) -> Self {
        overrides.fill_block(&mut self.inner);

        if let Some(hashes) = &overrides.block_hash {
            self.inner.db_mut().info.block_hashes.write().unwrap().extend(hashes)
        }

        self
    }

    /// Apply block overrides to the current block, if they are provided.
    ///
    /// Note that this is NOT reversible. The overrides are applied directly to
    /// the underlying state and these changes cannot be removed. If it is
    /// important that you have access to the pre-change state, you should wrap
    /// the existing DB in a new [`State`] and apply the overrides to that.
    pub fn maybe_apply_block_overrides(self, overrides: Option<&BlockOverrides>) -> Self {
        if let Some(overrides) = overrides {
            self.apply_block_overrides(overrides)
        } else {
            self
        }
    }
}
