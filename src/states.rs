use crate::Trevm;
use sealed::*;

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

pub(crate) mod sealed {
    macro_rules! states {
        ($($name:ident),+) => {
            $(

                /// A state for the [`Trevm`].
                ///
                /// [`Trevm`]: crate::Trevm
                #[allow(unnameable_types)]
                #[derive(Debug)]
                pub struct $name { _private: () }

                impl $name {
                    /// Create a new state.
                    pub(crate) fn new() -> Self {
                        Self { _private: () }
                    }
                }

            )*
        };
    }

    states!(NeedsCfg, NeedsFirstBlock, NeedsNextBlock, NeedsTx, Ready);

    /// Trait for states where block execution can be started.
    #[allow(unnameable_types)]
    pub trait NeedsBlock {}
    impl NeedsBlock for NeedsFirstBlock {}
    impl NeedsBlock for NeedsNextBlock {}

    /// Trait for states where thcare outputs vec is non-empty.
    #[allow(unnameable_types)]
    pub trait HasOutputs {}
    impl HasOutputs for NeedsNextBlock {}
    impl HasOutputs for NeedsTx {}
    impl HasOutputs for Ready {}

    #[allow(unnameable_types)]
    pub trait HasCfg {}
    #[allow(unnameable_types)]
    impl HasCfg for NeedsFirstBlock {}
    impl HasCfg for NeedsNextBlock {}
    impl HasCfg for NeedsTx {}
    impl HasCfg for Ready {}
}
