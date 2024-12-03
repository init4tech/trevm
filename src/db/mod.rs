mod sync_state;
pub use sync_state::{ConcurrentState, StateInfo};

mod cache_state;
pub use cache_state::ConcurrentCacheState;

use crate::{EvmNeedsBlock, Trevm};
use revm::{
    db::{states::bundle_state::BundleRetention, BundleState},
    DatabaseRef,
};

impl<Ext, Db: DatabaseRef, TrevmState> Trevm<'_, Ext, ConcurrentState<Db>, TrevmState> {
    /// Set the [EIP-161] state clear flag, activated in the Spurious Dragon
    /// hardfork.
    pub fn set_state_clear_flag(&mut self, flag: bool) {
        self.inner.db_mut().set_state_clear_flag(flag)
    }
}

impl<Ext, Db: DatabaseRef> EvmNeedsBlock<'_, Ext, ConcurrentState<Db>> {
    /// Finish execution and return the outputs.
    ///
    /// ## Panics
    ///
    /// If the State has not been built with StateBuilder::with_bundle_update.
    ///
    /// See [`State::merge_transitions`] and [`State::take_bundle`].
    pub fn finish(self) -> BundleState {
        let Self { inner: mut evm, .. } = self;
        evm.db_mut().merge_transitions(BundleRetention::Reverts);
        let bundle = evm.db_mut().take_bundle();

        bundle
    }
}
