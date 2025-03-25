use crate::{driver::BundleDriver, BlockDriver, ChainDriver, Trevm};
use revm::{
    context::{result::EVMError, ContextTr},
    Database,
};
use sealed::*;

/// A [`Trevm`] that requires a [`Cfg`].
///
/// Expected continuations include:
/// - [`EvmNeedsCfg::fill_cfg`]
///
/// [`Cfg`]: crate::Cfg
pub type EvmNeedsCfg<Ctx, Insp, Inst, Prec> = Trevm<Ctx, Insp, Inst, Prec, NeedsCfg>;

/// A [`Trevm`] that requires a [`Block`] and contains no
/// outputs. This EVM has not yet executed any transactions or state changes.
///
/// Expected continuations include:
/// - [`EvmNeedsBlock::fill_block`]
/// - [`EvmNeedsBlock::drive_block`]
/// - [`EvmNeedsBlock::drive_chain`]
///
/// [`Block`]: crate::Block
pub type EvmNeedsBlock<Ctx, Insp, Inst, Prec> = Trevm<Ctx, Insp, Inst, Prec, NeedsBlock>;

/// A [`Trevm`] that requires a [`Tx`].
///
/// Expected continuations include:
/// - [`EvmNeedsTx::fill_tx`]
/// - [`EvmNeedsTx::run_tx`]
/// - [`EvmNeedsTx::finish`]
///
/// [`Tx`]: crate::Tx
pub type EvmNeedsTx<Ctx, Insp, Inst, Prec> = Trevm<Ctx, Insp, Inst, Prec, NeedsTx>;

/// A [`Trevm`] that is ready to execute a transaction.
///
/// The transaction may be executed with [`EvmReady::run`] or cleared
/// with [`EvmReady::clear_tx`]
pub type EvmReady<Ctx, Insp, Inst, Prec> = Trevm<Ctx, Insp, Inst, Prec, Ready>;

/// A [`Trevm`] that run a transaction, and contains the resulting execution
/// details and state.
///
/// Expected continuations include:
/// - [`EvmTransacted::reject`]
/// - [`EvmTransacted::accept`]
pub type EvmTransacted<Ctx, Insp, Inst, Prec> = Trevm<Ctx, Insp, Inst, Prec, TransactedState>;

/// A [`Trevm`] that encountered an error during transaction execution.
///
/// Expected continuations include:
/// - [`EvmErrored::discard_error`]
/// - [`EvmErrored::into_error`]
pub type EvmErrored<
    Ctx,
    Insp,
    Inst,
    Prec,
    E = EVMError<<<Ctx as ContextTr>::Db as Database>::Error>,
> = Trevm<Ctx, Insp, Inst, Prec, ErroredState<E>>;

/// A [`Trevm`] that encountered an error during [`BlockDriver`] execution.
///
/// This is an [`EvmErrored`] parameterized with the driver's error type.
pub type EvmBlockDriverErrored<Ctx, Insp, Inst, Prec, T> =
    EvmErrored<Ctx, Insp, Inst, Prec, <T as BlockDriver<Insp>>::Error<<Ctx as ContextTr>::Db>>;

/// A [`Trevm`] that encountered an error during [`ChainDriver`] execution.
///
/// This is an [`EvmErrored`] parameterized with the driver's error type.
pub type EvmChainDriverErrored<Ctx, Insp, Inst, Prec, T> =
    EvmErrored<Ctx, Insp, Inst, Prec, <T as ChainDriver<Insp>>::Error<<Ctx as ContextTr>::Db>>;

/// A [`Trevm`] that encountered an error during [`BundleDriver`] execution.
///
/// This is an [`EvmErrored`] parameterized with the driver's error type.
pub type EvmBundleDriverErrored<Ctx, Insp, Inst, Prec, T> =
    EvmErrored<Ctx, Insp, Inst, Prec, <T as BundleDriver<Insp>>::Error<<Ctx as ContextTr>::Db>>;

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
/// use revm::db::InMemoryDB;
///
/// // produces types that look like this:
/// // type EvmNeedsCfg = trevm::EvmNeedsCfg<'static, (), InMemoryDB>;
/// trevm_aliases!(revm::db::InMemoryDB);
/// ```
///
/// Invoking with an ext and DB type will use the provided ext type and the
/// static lifetime:
///
/// ```
/// # mod t {
/// # use trevm::trevm_aliases;
/// # use revm::db::InMemoryDB;
/// # pub struct SomeExtType;
/// // produces types that look like this:
/// // type EvmNeedsCfg = trevm::EvmNeedsCfg<'static, SomeExtType, InMemoryDB>;
/// trevm_aliases!(SomeExtType, InMemoryDB);
/// # }
/// ```
///
/// To add a lifetime to the ext type, add the word lifetime:
///
/// ```
/// # mod t {
/// # use trevm::trevm_aliases;
/// # use revm::db::InMemoryDB;
/// # pub struct SomeExtType;
/// // produces types that look like this:
/// // type EvmNeedsCfg<'a> = trevm::EvmNeedsCfg<SomeExtType, InMemoryDB>;
/// trevm_aliases!(lifetime: SomeExtType, InMemoryDB);
/// # }
/// ```
macro_rules! trevm_aliases {
    ($db:ty) => {
        trevm_aliases!((), $db);
    };

    (lifetime: $ext:ty, $db:ty) => {
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
            pub type EvmNeedsCfg<'a> = $crate::EvmNeedsCfg<$ext, $db>;

            /// A [`Trevm`] that requires a [`Block`] and contains no
            /// outputs. This EVM has not yet executed any transactions or state changes.
            ///
            /// Expected continuations include:
            /// - [`EvmNeedsBlock::open_block`]
            /// - [`EvmNeedsBlock::drive_block`]
            /// - [`EvmNeedsBlock::drive_chain`]
            ///
            /// [`Block`]: crate::Block
            pub type EvmNeedsBlock<'a> = $crate::EvmNeedsBlock<$ext, $db>;

            /// A [`Trevm`] that requires a [`Tx`].
            ///
            /// Expected continuations include:
            /// - [`EvmNeedsTx::fill_tx`]
            /// - [`EvmNeedsTx::execute_tx`]
            /// - [`EvmNeedsTx::apply_tx`]
            /// - [`EvmNeedsTx::finish`]
            ///
            /// [`Tx`]: crate::Tx
            pub type EvmNeedsTx<'a> = $crate::EvmNeedsTx<$ext, $db>;

            /// A [`Trevm`] that is ready to execute a transaction.
            ///
            /// The transaction may be executed with [`Trevm::execute_tx`] or
            /// cleared with [`Trevm::clear_tx`]
            pub type EvmReady<'a> = $crate::EvmReady<$ext, $db>;

            /// A [`Trevm`] that encountered an error during transaction execution.
            ///
            /// Expected continuations include:
            /// - [`EvmTransacted::reject`]
            /// - [`EvmTransacted::accept`]
            pub type EvmTransacted<'a> = $crate::EvmTransacted<$ext, $db>;

            /// A [`Trevm`] that encountered an error during transaction execution.
            ///
            /// Expected continuations include:
            /// - [`EvmErrored::discard_error`]
            /// - [`EvmErrored::into_error`]
            pub type EvmErrored<
                'a,
                E = $crate::revm::primitives::EVMError<<$db as $crate::revm::Database>::Error>,
            > = $crate::EvmErrored<$ext, $db, E>;

            /// A [`Trevm`] that encountered an error during [`BlockDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmBlockDriverErrored<T> = $crate::EvmBlockDriverErrored<$ext, $db, T>;

            /// A [`Trevm`] that encountered an error during [`ChainDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmChainDriverErrored<T> = $crate::EvmChainDriverErrored<$ext, $db, T>;

            /// A [`Trevm`] that encountered an error during [`BundleDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmBundleDriverErrored<T> = $crate::EvmBundleDriverErrored<$ext, $db, T>;
        }
    };

    ($ext:ty, $db:ty) => {
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
            pub type EvmNeedsCfg = $crate::EvmNeedsCfg<'static, $ext, $db>;

            /// A [`Trevm`] that requires a [`Block`].
            ///
            /// Expected continuations include:
            /// - [`EvmNeedsBlock::open_block`]
            ///
            /// [`Block`]: crate::Block
            pub type EvmNeedsBlock = $crate::EvmNeedsBlock<'static, $ext, $db>;

            /// A [`Trevm`] that requires a [`Tx`].
            //
            /// Expected continuations include:
            /// - [`EvmNeedsTx::fill_tx`]
            /// - [`EvmNeedsTx::execute_tx`]
            /// - [`EvmNeedsTx::apply_tx`]
            /// - [`EvmNeedsTx::finish`]
            ///
            /// [`Tx`]: crate::Tx
            pub type EvmNeedsTx = $crate::EvmNeedsTx<'static, $ext, $db>;

            /// A [`Trevm`] that is ready to execute a transaction.
            ///
            /// The transaction may be executed with [`Trevm::execute_tx`] or
            /// cleared with [`Trevm::clear_tx`]
            pub type EvmReady = $crate::EvmReady<'static, $ext, $db>;

            /// A [`Trevm`] that encountered an error during transaction execution.
            ///
            /// Expected continuations include:
            /// - [`EvmTransacted::reject`]
            /// - [`EvmTransacted::accept`]
            pub type EvmTransacted = $crate::EvmTransacted<'static, $ext, $db>;

            /// A [`Trevm`] that encountered an error during transaction execution.
            ///
            /// Expected continuations include:
            /// - [`EvmErrored::discard_error`]
            /// - [`EvmErrored::into_error`]
            pub type EvmErrored<E> = $crate::EvmErrored<'static, $ext, $db, E>;

            /// A [`Trevm`] that encountered an error during [`BlockDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmBlockDriverErrored<T> =
                $crate::EvmBlockDriverErrored<'static, $ext, $db, T>;

            /// A [`Trevm`] that encountered an error during [`ChainDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmChainDriverErrored<T> =
                $crate::EvmChainDriverErrored<'static, $ext, $db, T>;

            /// A [`Trevm`] that encountered an error during [`BundleDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmBundleDriverErrored<T> =
                $crate::EvmBundleDriverErrored<'static, $ext, $db, T>;
        }
    };
}
