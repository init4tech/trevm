use crate::{BlockContext, BlockDriver, ChainDriver, Trevm};
use sealed::*;

/// A [`Trevm`] that requires a [`Cfg`].
///
/// Expected continuations include:
/// - [`EvmNeedsCfg::fill_cfg`]
///
/// [`Cfg`]: crate::Cfg
pub type EvmNeedsCfg<'a, Ext, Db> = Trevm<'a, Ext, Db, NeedsCfg>;

/// A [`Trevm`] that requires a [`Block`] and contains no
/// outputs. This EVM has not yet executed any transactions or state changes.
///
/// Expected continuations include:
/// - [`EvmNeedsBlock::open_block`]
/// - [`EvmNeedsBlock::drive_block`]
/// - [`EvmNeedsBlock::drive_chain`]
///
/// [`Block`]: crate::Block
pub type EvmNeedsBlock<'a, Ext, Db> = Trevm<'a, Ext, Db, NeedsBlock>;

/// A [`Trevm`] that has completed a block and contains the block's populated
/// lifecycle object.
///
/// Expected continuations include:
/// - [`EvmBlockComplete::take_context`]
/// - [`EvmBlockComplete::discard_context`]
pub type EvmBlockComplete<'a, Ext, Db, T> = Trevm<'a, Ext, Db, BlockComplete<T>>;

/// A [`Trevm`] that requires a [`Tx`].
///
/// Expected continuations include:
/// - [`EvmNeedsTx::fill_tx`]
/// - [`EvmNeedsTx::run_tx`]
/// - [`EvmNeedsTx::finish`]
///
/// [`Tx`]: crate::Tx
pub type EvmNeedsTx<'a, Ext, Db, C> = Trevm<'a, Ext, Db, NeedsTx<C>>;

/// A [`Trevm`] that is ready to execute a transaction.
///
/// The transaction may be executed with [`EvmReady::run`] or cleared
/// with [`EvmReady::clear_tx`]
pub type EvmReady<'a, Ext, Db, C> = Trevm<'a, Ext, Db, Ready<C>>;

/// A [`Trevm`] that encountered an error during transaction execution.
///
/// Expected continuations include:
/// - [`EvmTransacted::reject`]
/// - [`EvmTransacted::accept`]
pub type EvmTransacted<'a, Ext, Db, C> = Trevm<'a, Ext, Db, TransactedState<C>>;

/// A [`Trevm`] that encountered an error during transaction execution.
///
/// Expected continuations include:
/// - [`EvmErrored::discard_error`]
/// - [`EvmErrored::into_error`]
pub type EvmErrored<'a, Ext, Db, C, E = <C as BlockContext<Ext>>::Error<Db>> =
    Trevm<'a, Ext, Db, ErroredState<C, E>>;

/// A [`Trevm`] that encountered an error during [`BlockDriver`] execution.
///
/// This is an [`EvmErrored`] parameterized with the driver's error type.
pub type EvmBlockDriverErrored<'a, 'b, Ext, Db, C, T> =
    EvmErrored<'a, Ext, Db, C, <T as BlockDriver<'b, Ext, C>>::Error<Db>>;

/// A [`Trevm`] that encountered an error during [`ChainDriver`] execution.
///
/// This is an [`EvmErrored`] parameterized with the driver's error type.
pub type EvmChainDriverErrored<'a, 'b, Ext, Db, C, T> =
    EvmErrored<'a, Ext, Db, C, <T as ChainDriver<'b, Ext, C>>::Error<Db>>;

#[allow(unnameable_types, dead_code, unreachable_pub)]
pub(crate) mod sealed {
    use revm::primitives::ResultAndState;

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

    states!(NeedsCfg, NeedsBlock);

    /// A state for the [`Trevm`].
    ///
    /// [`Trevm`]: crate::Trevm
    #[derive(Debug)]
    pub struct NeedsTx<T>(pub T);

    /// A state for the [`Trevm`].
    ///
    /// [`Trevm`]: crate::Trevm
    #[derive(Debug)]
    pub struct Ready<T>(pub T);

    /// A state for the [`Trevm`].
    ///
    /// [`Trevm`]: crate::Trevm
    #[derive(Debug)]
    pub struct BlockComplete<T>(pub T);

    /// A state for the [`Trevm`].
    ///
    /// [`Trevm`]: crate::Trevm
    #[derive(Debug)]
    pub struct TransactedState<T> {
        /// The context for the block.
        pub context: T,
        /// The transaction result.
        pub result: ResultAndState,
    }

    /// A state for the [`Trevm`].
    ///
    /// [`Trevm`]: crate::Trevm
    #[derive(Debug)]
    pub struct ErroredState<T, E> {
        /// The context for the block.
        pub context: T,
        /// The transaction error.
        pub error: E,
    }

    pub struct Seal;

    pub trait HasCfg {}
    impl HasCfg for NeedsBlock {}
    impl<T> HasCfg for NeedsTx<T> {}
    impl<T> HasCfg for TransactedState<T> {}
    impl<T, E> HasCfg for ErroredState<T, E> {}
    impl<T> HasCfg for Ready<T> {}

    pub trait HasBlock {}
    impl<T> HasBlock for NeedsTx<T> {}
    impl<T> HasBlock for TransactedState<T> {}
    impl<T, E> HasBlock for ErroredState<T, E> {}
    impl<T> HasBlock for Ready<T> {}

    pub trait HasTx {}
    impl<T> HasTx for TransactedState<T> {}
    impl<T, E> HasTx for ErroredState<T, E> {}
    impl<T> HasTx for Ready<T> {}

    pub trait HasContext {
        type Context;

        fn context(&self) -> &Self::Context;

        fn context_mut(&mut self) -> &mut Self::Context;

        fn take_context(self) -> Self::Context
        where
            Self: Sized;
    }

    impl<T> HasContext for NeedsTx<T> {
        type Context = T;

        fn context(&self) -> &Self::Context {
            &self.0
        }

        fn context_mut(&mut self) -> &mut Self::Context {
            &mut self.0
        }

        fn take_context(self) -> Self::Context {
            self.0
        }
    }

    impl<T> HasContext for BlockComplete<T> {
        type Context = T;

        fn context(&self) -> &Self::Context {
            &self.0
        }

        fn context_mut(&mut self) -> &mut Self::Context {
            &mut self.0
        }

        fn take_context(self) -> Self::Context {
            self.0
        }
    }

    impl<T> HasContext for TransactedState<T> {
        type Context = T;

        fn context(&self) -> &Self::Context {
            &self.context
        }

        fn context_mut(&mut self) -> &mut Self::Context {
            &mut self.context
        }

        fn take_context(self) -> Self::Context {
            self.context
        }
    }

    impl<T, E> HasContext for ErroredState<T, E> {
        type Context = T;

        fn context(&self) -> &Self::Context {
            &self.context
        }

        fn context_mut(&mut self) -> &mut Self::Context {
            &mut self.context
        }

        fn take_context(self) -> Self::Context {
            self.context
        }
    }

    impl<T> HasContext for Ready<T> {
        type Context = T;

        fn context(&self) -> &Self::Context {
            &self.0
        }

        fn context_mut(&mut self) -> &mut Self::Context {
            &mut self.0
        }

        fn take_context(self) -> Self::Context {
            self.0
        }
    }
}

#[macro_export]
/// Declare type aliases for trevm with a concrete `Ext` and `Db` type.
///
/// This will create aliases with your concrete types for the following types:
/// - [`EvmNeedsCfg`]
/// - [`EvmNeedsBlock`]
/// - [`EvmBlockComplete`]
/// - [`EvmNeedsTx`]
/// - [`EvmReady`]
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
/// // type EvmNeedsCfg<'a> = trevm::EvmNeedsCfg<'a, SomeExtType, InMemoryDB>;
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
            use $crate::{Block, BlockDriver, Cfg, ChainDriver, Trevm, Tx};

            /// A [`Trevm`] that requires a [`Cfg`].
            ///
            /// Expected continuations include:
            /// - [`Trevm::fill_cfg`]
            ///
            /// [`Cfg`]: crate::Cfg
            /// [`Trevm`]: crate::Trevm
            pub type EvmNeedsCfg<'a> = $crate::EvmNeedsCfg<'a, $ext, $db>;

            /// A [`Trevm`] that requires a [`Block`] and contains no
            /// outputs. This EVM has not yet executed any transactions or state changes.
            ///
            /// Expected continuations include:
            /// - [`EvmNeedsBlock::open_block`]
            /// - [`EvmNeedsBlock::drive_block`]
            /// - [`EvmNeedsBlock::drive_chain`]
            ///
            /// [`Block`]: crate::Block
            pub type EvmNeedsBlock<'a> = $crate::EvmNeedsBlock<'a, $ext, $db>;

            /// A [`Trevm`] that has completed a block and contains the block's populated
            /// lifecycle object.
            ///
            /// Expected continuations include:
            /// - [`EvmBlockComplete::into_parts`]
            /// - [`EvmBlockComplete::discard_context`]
            pub type EvmBlockComplete<'a, C> = $crate::EvmBlockComplete<'a, $ext, $db, C>;

            /// A [`Trevm`] that requires a [`Tx`].
            ///
            /// Expected continuations include:
            /// - [`EvmNeedsTx::fill_tx`]
            /// - [`EvmNeedsTx::execute_tx`]
            /// - [`EvmNeedsTx::apply_tx`]
            /// - [`EvmNeedsTx::finish`]
            ///
            /// [`Tx`]: crate::Tx
            pub type EvmNeedsTx<'a, C> = $crate::EvmNeedsTx<'a, $ext, $db, C>;

            /// A [`Trevm`] that is ready to execute a transaction.
            ///
            /// The transaction may be executed with [`Trevm::execute_tx`] or
            /// cleared with [`Trevm::clear_tx`]
            pub type EvmReady<'a, C> = $crate::EvmReady<'a, $ext, $db, C>;

            /// A [`Trevm`] that encountered an error during transaction execution.
            ///
            /// Expected continuations include:
            /// - [`EvmTransacted::reject`]
            /// - [`EvmTransacted::accept`]
            pub type EvmTransacted<'a, C> = $crate::EvmTransacted<'a, $ext, $db, C>;

            /// A [`Trevm`] that encountered an error during transaction execution.
            ///
            /// Expected continuations include:
            /// - [`EvmErrored::discard_error`]
            /// - [`EvmErrored::into_error`]
            pub type EvmErrored<'a, C, E = <C as $crate::BlockContext<$ext>>::Error<$db>> =
                $crate::EvmErrored<'a, $ext, $db, C, E>;

            /// A [`Trevm`] that encountered an error during [`BlockDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmBlockDriverErrored<'a, 'b, C, T> =
                $crate::EvmBlockDriverErrored<'a, 'b, $ext, $db, C, T>;

            /// A [`Trevm`] that encountered an error during [`ChainDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmChainDriverErrored<'a, 'b, C, T> =
                $crate::EvmChainDriverErrored<'a, 'b, $ext, $db, C, T>;
        }
    };

    ($ext:ty, $db:ty) => {
        #[allow(unused_imports, unreachable_pub, dead_code)]
        pub use __aliases::*;

        #[allow(unused_imports, unreachable_pub, dead_code)]
        mod __aliases {
            use super::*;
            // bring these in scope so that doclinks work in generated docs
            use $crate::{Block, BlockDriver, Cfg, ChainDriver, Trevm, Tx};

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

            /// A [`Trevm`] that has completed a block and contains the block's populated
            /// lifecycle object.
            ///
            /// Expected continuations include:
            /// - [`EvmBlockComplete::into_parts`]
            /// - [`EvmBlockComplete::discard_context`]
            pub type EvmBlockComplete<C> = $crate::EvmBlockComplete<'static, $ext, $db, C>;

            /// A [`Trevm`] that requires a [`Tx`].
            //
            /// Expected continuations include:
            /// - [`EvmNeedsTx::fill_tx`]
            /// - [`EvmNeedsTx::execute_tx`]
            /// - [`EvmNeedsTx::apply_tx`]
            /// - [`EvmNeedsTx::finish`]
            ///
            /// [`Tx`]: crate::Tx
            pub type EvmNeedsTx<C> = $crate::EvmNeedsTx<'static, $ext, $db, C>;

            /// A [`Trevm`] that is ready to execute a transaction.
            ///
            /// The transaction may be executed with [`Trevm::execute_tx`] or
            /// cleared with [`Trevm::clear_tx`]
            pub type EvmReady<C> = $crate::EvmReady<'static, $ext, $db, C>;

            /// A [`Trevm`] that encountered an error during transaction execution.
            ///
            /// Expected continuations include:
            /// - [`EvmTransacted::reject`]
            /// - [`EvmTransacted::accept`]
            pub type EvmTransacted<C> = $crate::EvmTransacted<'static, $ext, $db, C>;

            /// A [`Trevm`] that encountered an error during transaction execution.
            ///
            /// Expected continuations include:
            /// - [`EvmErrored::discard_error`]
            /// - [`EvmErrored::into_error`]
            pub type EvmErrored<C, E = <C as $crate::BlockContext<$ext>>::Error<$db>> =
                $crate::EvmErrored<'static, $ext, $db, C, E>;

            /// A [`Trevm`] that encountered an error during [`BlockDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmBlockDriverErrored<'a, C, T> =
                $crate::EvmBlockDriverErrored<'static, 'a, $ext, $db, C, T>;

            /// A [`Trevm`] that encountered an error during [`ChainDriver`] execution.
            ///
            /// This is an [`EvmErrored`] parameterized with the driver's error type.
            pub type EvmChainDriverErrored<'a, C, T> =
                $crate::EvmChainDriverErrored<'static, 'a, $ext, $db, C, T>;
        }
    };
}
