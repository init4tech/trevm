pub(crate) mod sealed {
    macro_rules! states {
        ($($name:ident),+) => {
            $(
                /// A state for the [`Trevm`].
                ///
                /// [`Trevm`]: crate::Trevm
                pub struct $name { _private: () }
            )*
        };
    }

    states!(NeedsCfg, NeedsFirstBlock, NeedsNextBlock, NeedsTx, Ready);

    /// Trait for states where block execution can be started.
    pub trait NeedsBlock {}
    impl NeedsBlock for NeedsFirstBlock {}
    impl NeedsBlock for NeedsNextBlock {}

    /// Trait for states where thcare outputs vec is non-empty.
    pub trait HasOutputs {}
    impl HasOutputs for NeedsNextBlock {}
    impl HasOutputs for NeedsTx {}
    impl HasOutputs for Ready {}

    pub trait HasCfg {}
    impl HasCfg for NeedsFirstBlock {}
    impl HasCfg for NeedsNextBlock {}
    impl HasCfg for NeedsTx {}
    impl HasCfg for Ready {}
}
use sealed::*;

use crate::Trevm;

/// A [`Trevm`] that requires a [`Cfg`].
///
/// Expected continuations include:
/// - [`Trevm::fill_cfg`]
///
/// [`Cfg`]: crate::Cfg
pub type EvmNeedsCfg<'a, Ext, Db> = Trevm<'a, Ext, Db, NeedsCfg>;

/// A [`Trevm`] that requires a [`Block`] and contains no
/// outputs. This EVM has not yet executed any transactions or state changes.
///
/// Expected continuations include:
/// - [`EvmNeedsFirstBlock::fill_block`]
/// - [`EvmNeedsFirstBlock::open_block`]
///
/// [`Block`]: crate::Block
pub type EvmNeedsFirstBlock<'a, Ext, Db> = Trevm<'a, Ext, Db, NeedsFirstBlock>;

/// A [`Trevm`] that requires a [`Block`].
///
/// Expected continuations include:
/// - [`EvmNeedsNextBlock::fill_block`]
/// - [`EvmNeedsFirstBlock::open_block`]
///
/// [`Block`]: crate::Block
pub type EvmNeedsNextBlock<'a, Ext, Db> = Trevm<'a, Ext, Db, NeedsNextBlock>;

/// A [`Trevm`] that requires a [`Tx`].
///
/// Expected continuations include:
/// - [`EvmNeedsTx::fill_tx`]
/// - [`EvmNeedsTx::clear_block`]
/// - [`EvmNeedsTx::execute_tx`]
/// - [`EvmNeedsTx::apply_tx`]
/// - [`EvmNeedsTx::finish`]
///
/// [`Tx`]: crate::Tx
pub type EvmNeedsTx<'a, Ext, Db> = Trevm<'a, Ext, Db, NeedsTx>;

/// A [`Trevm`] that is ready to execute a transaction.
///
/// The transaction may be executed with [`Trevm::execute_tx`] or cleared
/// with [`Trevm::clear_tx`]
pub type EvmReady<'a, Ext, Db> = Trevm<'a, Ext, Db, Ready>;
