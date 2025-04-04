use crate::{driver::BundleDriver, BlockDriver, ChainDriver, Trevm};
use revm::{context::result::EVMError, inspector::NoOpInspector, Database};
use sealed::*;

/// A [`Trevm`] that requires a [`Cfg`].
///
/// Expected continuations include:
/// - [`EvmNeedsCfg::fill_cfg`]
///
/// [`Cfg`]: crate::Cfg
pub type EvmNeedsCfg<Db, Insp = NoOpInspector> = Trevm<Db, Insp, NeedsCfg>;

/// A [`Trevm`] that requires a [`Block`] and contains no
/// outputs. This EVM has not yet executed any transactions or state changes.
///
/// Expected continuations include:
/// - [`EvmNeedsBlock::fill_block`]
/// - [`EvmNeedsBlock::drive_block`]
/// - [`EvmNeedsBlock::drive_chain`]
///
/// [`Block`]: crate::Block
pub type EvmNeedsBlock<Db, Insp = NoOpInspector> = Trevm<Db, Insp, NeedsBlock>;

/// A [`Trevm`] that requires a [`Tx`].
///
/// Expected continuations include:
/// - [`EvmNeedsTx::fill_tx`]
/// - [`EvmNeedsTx::run_tx`]
/// - [`EvmNeedsTx::finish`]
///
/// [`Tx`]: crate::Tx
pub type EvmNeedsTx<Db, Insp = NoOpInspector> = Trevm<Db, Insp, NeedsTx>;

/// A [`Trevm`] that is ready to execute a transaction.
///
/// The transaction may be executed with [`EvmReady::run`] or cleared
/// with [`EvmReady::clear_tx`]
pub type EvmReady<Db, Insp = NoOpInspector> = Trevm<Db, Insp, Ready>;

/// A [`Trevm`] that run a transaction, and contains the resulting execution
/// details and state.
///
/// Expected continuations include:
/// - [`EvmTransacted::reject`]
/// - [`EvmTransacted::accept`]
pub type EvmTransacted<Db, Insp = NoOpInspector> = Trevm<Db, Insp, TransactedState>;

/// A [`Trevm`] that encountered an error during transaction execution.
///
/// Expected continuations include:
/// - [`EvmErrored::discard_error`]
/// - [`EvmErrored::into_error`]
pub type EvmErrored<Db, Insp = NoOpInspector, E = EVMError<<Db as Database>::Error>> =
    Trevm<Db, Insp, ErroredState<E>>;

/// A [`Trevm`] that encountered an error during [`BlockDriver`] execution.
///
/// This is an [`EvmErrored`] parameterized with the driver's error type.
pub type EvmBlockDriverErrored<T, Db, Insp = NoOpInspector> =
    EvmErrored<Db, Insp, <T as BlockDriver<Db, Insp>>::Error>;

/// A [`Trevm`] that encountered an error during [`ChainDriver`] execution.
///
/// This is an [`EvmErrored`] parameterized with the driver's error type.
pub type EvmChainDriverErrored<T, Db, Insp = NoOpInspector> =
    EvmErrored<Db, Insp, <T as ChainDriver<Db, Insp>>::Error>;

/// A [`Trevm`] that encountered an error during [`BundleDriver`] execution.
///
/// This is an [`EvmErrored`] parameterized with the driver's error type.
pub type EvmBundleDriverErrored<T, Db, Insp = NoOpInspector> =
    EvmErrored<Db, Insp, <T as BundleDriver<Db, Insp>>::Error>;

#[allow(unnameable_types, dead_code, unreachable_pub)]
pub(crate) mod sealed {
    use revm::context::result::ResultAndState;

    macro_rules! states {
        ($($name:ident),+) => {
            $(

                /// A state for the [`Trevm`].
                ///
                /// [`Trevm`]: crate::Trevm
                #[derive(Debug, Copy, Clone)]
                pub struct $name { _private: () }

                impl $name {
                    /// Create a new state.
                    pub(crate) const fn new() -> Self {
                        Self { _private: () }
                    }
                }

            )*
        };
    }

    states!(NeedsCfg, NeedsBlock, NeedsTx, Ready);

    /// A state for the [`Trevm`].
    ///
    /// [`Trevm`]: crate::Trevm
    #[derive(Debug, Clone)]
    pub struct TransactedState {
        /// The transaction result.
        pub result: ResultAndState,
    }

    /// A state for the [`Trevm`].
    ///
    /// [`Trevm`]: crate::Trevm
    #[derive(Debug, Copy, Clone)]
    pub struct ErroredState<E> {
        /// The transaction error.
        pub error: E,
    }

    pub struct Seal;

    pub trait HasCfg {}
    impl HasCfg for NeedsBlock {}
    impl HasCfg for NeedsTx {}
    impl HasCfg for TransactedState {}
    impl<E> HasCfg for ErroredState<E> {}
    impl HasCfg for Ready {}

    pub trait HasBlock: HasCfg {}
    impl HasBlock for NeedsTx {}
    impl HasBlock for TransactedState {}
    impl<E> HasBlock for ErroredState<E> {}
    impl HasBlock for Ready {}

    pub trait HasTx: HasBlock + HasCfg {}
    impl HasTx for TransactedState {}
    impl<E> HasTx for ErroredState<E> {}
    impl HasTx for Ready {}
}

#[macro_export]
/// Declare type aliases for trevm with a concrete `Ext` and `Db` type.
///
/// This will create aliases with your concrete types for the following types:
/// - [`EvmNeedsCfg`]
/// - [`EvmNeedsBlock`]
/// - [`EvmNeedsTx`]
/// - [`EvmReady`]
/// - [`EvmTransacted`]
/// - [`EvmErrored`]
/// - [`EvmBlockDriverErrored`]
/// - [`EvmChainDriverErrored`]
/// - [`EvmBundleDriverErrored`]
///
/// ## Basic usage:
///
/// Invoking with just a DB type will use [`()`] for the ext
///
/// ```
/// use trevm::trevm_aliases;
/// use revm::database::in_memory_db::InMemoryDB;
///
/// // produces types that look like this:
/// // type EvmNeedsCfg = trevm::EvmNeedsCfg<InMemoryDB, ()>
/// trevm_aliases!(revm::database::in_memory_db::InMemoryDB);
/// ```
///
/// Invoking with an ext and DB type will use the provided ext type and the
/// static lifetime:
///
/// ```
/// # mod t {
/// # use trevm::trevm_aliases;
/// # use revm::database::in_memory_db::InMemoryDB;
/// # pub struct SomeExtType;
/// // produces types that look like this:
/// // type EvmNeedsCfg = trevm::EvmNeedsCfg<InMemoryDb, SomeExtType>
/// trevm_aliases!(revm::database::in_memory_db::InMemoryDB, SomeExtType);
/// # }
/// ```
macro_rules! trevm_aliases {
    ($db:ty) => {
        trevm_aliases!((), $db);
    };

    ($db:ty, $insp:ty) => {
        #[allow(unused_imports, unreachable_pub, dead_code)]
        pub use __aliases::*;

        #[allow(unused_imports, unreachable_pub, dead_code)]
        mod __aliases {
            use super::*;
            // bring these in scope so that doclinks work in generated docs
            use $crate::{Block, BlockDriver, ChainDriver, Trevm, Tx};

            /// A [`Trevm`] that requires a [`Cfg`].
            ///
            /// Expected continuations include:
            /// - [`Trevm::fill_cfg`]
            ///
            /// [`Cfg`]: crate::Cfg
            /// [`Trevm`]: crate::Trevm
            pub type EvmNeedsCfg = $crate::EvmNeedsCfg<$db, $insp>;

            /// A [`Trevm`] that requires a [`Block`].
            ///
            /// Expected continuations include:
            /// - [`EvmNeedsBlock::open_block`]
            ///
            /// [`Block`]: crate::Block
            pub type EvmNeedsBlock = $crate::EvmNeedsBlock<$db, $insp>;

            /// A [`Trevm`] that requires a [`Tx`].
            //
            /// Expected continuations include:
            /// - [`EvmNeedsTx::fill_tx`]
            /// - [`EvmNeedsTx::execute_tx`]
            /// - [`EvmNeedsTx::apply_tx`]
            /// - [`EvmNeedsTx::finish`]
            ///
            /// [`Tx`]: crate::Tx
            pub type EvmNeedsTx = $crate::EvmNeedsTx<$db, $insp>;

            /// A [`Trevm`] that is ready to execute a transaction.
            ///
            /// The transaction may be executed with [`Trevm::execute_tx`] or
            /// cleared with [`Trevm::clear_tx`]
            pub type EvmReady = $crate::EvmReady<$db, $insp>;

            /// A [`Trevm`] that encountered an error during transaction execution.
            ///
            /// Expected continuations include:
            /// - [`EvmTransacted::reject`]
            /// - [`EvmTransacted::accept`]
            pub type EvmTransacted = $crate::EvmTransacted<$db, $insp>;

            /// A [`Trevm`] that encountered an error during transaction execution.
            ///
            /// Expected continuations include:
            /// - [`EvmErrored::discard_error`]
            /// - [`EvmErrored::into_error`]
            pub type EvmErrored<E> = $crate::EvmErrored<$db, $insp, E>;

            /// A [`Trevm`] that encountered an error during [`BlockDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmBlockDriverErrored<T> = $crate::EvmBlockDriverErrored<$db, $insp, T>;

            /// A [`Trevm`] that encountered an error during [`ChainDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmChainDriverErrored<T> = $crate::EvmChainDriverErrored<$db, $insp, T>;

            /// A [`Trevm`] that encountered an error during [`BundleDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmBundleDriverErrored<T> = $crate::EvmBundleDriverErrored<$db, $insp, T>;
        }
    };
}
