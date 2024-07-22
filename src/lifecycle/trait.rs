use crate::{Block, EvmNeedsTx, NeedsBlock, TransactedError, Trevm};
use revm::{primitives::EVMError, Database, DatabaseCommit};

/// Pre-block and post-block lifecycle events.
///
/// This trait encapsulates special pre-block and post-block logic that needs to
/// be applied to the EVM. This is useful for implementing EIPs that require
/// special system actions to be taken before and after the block is processed.
///
/// Lifecycles are provided for [Shanghai], [Cancun], and [Prague]. While most
/// lifecycles modify previous behavior, the [Prague] lifecycle is a superset of
/// the [Cancun] lifecycle, and the [Cancun] lifecycle is a superset of the
/// [Shanghai] lifecycle. This means that the [Prague] lifecycle includes all
/// the logic of the [Cancun] and [Shanghai] lifecycles.
///
/// [Shanghai]: crate::ShanghaiLifecycle
/// [Cancun]: crate::CancunLifecycle
/// [Prague]: crate::PragueLifecycle
pub trait Lifecycle<'a, Ext, Db: Database + DatabaseCommit> {
    /// The error type for the lifecycle. This captures logic errors that occur
    /// during the lifecycle.
    type Error: From<EVMError<Db::Error>>;

    /// Apply pre-block logic, and prep the EVM for the first user transaction.
    fn open_block<TrevmState: NeedsBlock, B: Block>(
        &mut self,
        trevm: Trevm<'a, Ext, Db, TrevmState>,
        b: &B,
    ) -> Result<EvmNeedsTx<'a, Ext, Db>, TransactedError<'a, Ext, Db, Self::Error>>;

    /// Apply post-block logic and close the block.
    fn close_block(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> Result<EvmNeedsTx<'a, Ext, Db>, TransactedError<'a, Ext, Db, Self::Error>>;
}
