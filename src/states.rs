use crate::{BlockContext, Trevm};
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
/// - [`EvmNeedsFirstBlock::open_block`]
///
/// [`Block`]: crate::Block
pub type EvmNeedsFirstBlock<'a, Ext, Db> = Trevm<'a, Ext, Db, NeedsFirstBlock>;

/// A [`Trevm`] that has completed a block and contains the block's populated
/// lifecycle object.
///
/// Expected continuations include:
/// - [`EvmBlockComplete::take_context`]
/// - [`EvmBlockComplete::discard_context`]
pub type EvmBlockComplete<'a, Ext, Db, T> = Trevm<'a, Ext, Db, BlockComplete<T>>;

/// A [`Trevm`] that requires a [`Block`].
///
/// Expected continuations include:
/// - [`EvmNeedsFirstBlock::open_block`]
///
/// [`Block`]: crate::Block
pub type EvmNeedsNextBlock<'a, Ext, Db> = Trevm<'a, Ext, Db, NeedsNextBlock>;

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
pub type EvmErrored<'a, Ext, Db, C, E = <C as BlockContext>::Error<Db>> =
    Trevm<'a, Ext, Db, ErroredState<C, E>>;

#[allow(unnameable_types, dead_code, unreachable_pub)]
pub(crate) mod sealed {
    use revm::primitives::ResultAndState;

    macro_rules! states {
        ($($name:ident),+) => {
            $(

                /// A state for the [`Trevm`].
                ///
                /// [`Trevm`]: crate::Trevm
                #[derive(Debug)]
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

    states!(NeedsCfg, NeedsFirstBlock, NeedsNextBlock);

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

    /// Trait for states where block execution can be started.
    pub trait NeedsBlock {}
    impl NeedsBlock for NeedsFirstBlock {}
    impl NeedsBlock for NeedsNextBlock {}

    /// Trait for states where thcare outputs vec is non-empty.
    pub trait HasOutputs {}
    impl HasOutputs for NeedsNextBlock {}
    impl<T> HasOutputs for NeedsTx<T> {}
    impl<T> HasOutputs for TransactedState<T> {}
    impl<T, E> HasOutputs for ErroredState<T, E> {}
    impl<T> HasOutputs for Ready<T> {}

    pub trait HasCfg {}
    impl HasCfg for NeedsFirstBlock {}
    impl HasCfg for NeedsNextBlock {}
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
    }

    impl<T> HasContext for NeedsTx<T> {
        type Context = T;

        fn context(&self) -> &Self::Context {
            &self.0
        }

        fn context_mut(&mut self) -> &mut Self::Context {
            &mut self.0
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
    }

    impl<T> HasContext for TransactedState<T> {
        type Context = T;

        fn context(&self) -> &Self::Context {
            &self.context
        }

        fn context_mut(&mut self) -> &mut Self::Context {
            &mut self.context
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
    }

    impl<T> HasContext for Ready<T> {
        type Context = T;

        fn context(&self) -> &Self::Context {
            &self.0
        }

        fn context_mut(&mut self) -> &mut Self::Context {
            &mut self.0
        }
    }
}

#[macro_export]
/// Declare type aliases for trevm with a concrete `Ext` and `Db` type.
///
/// This will create aliases with your concrete types for the following types:
/// - [`EvmNeedsCfg`]
/// - [`EvmNeedsFirstBlock`]
/// - [`EvmBlockComplete`]
/// - [`EvmNeedsNextBlock`]
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
            use $crate::Block;
            use $crate::Cfg;
            use $crate::Trevm;
            use $crate::Tx;

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
            /// - [`EvmNeedsFirstBlock::open_block`]
            ///
            /// [`Block`]: crate::Block
            pub type EvmNeedsFirstBlock<'a> = $crate::EvmNeedsFirstBlock<'a, $ext, $db>;

            /// A [`Trevm`] that has completed a block and contains the block's populated
            /// lifecycle object.
            ///
            /// Expected continuations include:
            /// - [`EvmBlockComplete::into_parts`]
            /// - [`EvmBlockComplete::discard_context`]
            pub type EvmBlockComplete<'a, C> = $crate::EvmBlockComplete<'a, $ext, $db, C>;

            /// A [`Trevm`] that requires a [`Block`].
            ///
            /// Expected continuations include:
            /// - [`EvmNeedsFirstBlock::open_block`]
            ///
            /// [`Block`]: crate::Block
            pub type EvmNeedsNextBlock<'a> = $crate::EvmNeedsNextBlock<'a, $ext, $db>;

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
            pub type EvmErrored<'a, C, E = <C as $crate::BlockContext<$ext, $db>>::Error> =
                $crate::EvmErrored<'a, $ext, $db, C, E>;
        }
    };

    ($ext:ty, $db:ty) => {
        #[allow(unused_imports, unreachable_pub, dead_code)]
        pub use __aliases::*;

        #[allow(unused_imports, unreachable_pub, dead_code)]
        mod __aliases {
            use super::*;
            // bring these in scope so that doclinks work in generated docs
            use $crate::Block;
            use $crate::Cfg;
            use $crate::Trevm;
            use $crate::Tx;

            /// A [`Trevm`] that requires a [`Cfg`].
            ///
            /// Expected continuations include:
            /// - [`Trevm::fill_cfg`]
            ///
            /// [`Cfg`]: crate::Cfg
            /// [`Trevm`]: crate::Trevm
            pub type EvmNeedsCfg = $crate::EvmNeedsCfg<'static, $ext, $db>;

            /// A [`Trevm`] that requires a [`Block`] and contains no
            /// outputs. This EVM has not yet executed any transactions or state changes.
            ///
            /// Expected continuations include:
            /// - [`EvmNeedsFirstBlock::open_block`]
            ///
            /// [`Block`]: crate::Block
            pub type EvmNeedsFirstBlock = $crate::EvmNeedsFirstBlock<'static, $ext, $db>;

            /// A [`Trevm`] that has completed a block and contains the block's populated
            /// lifecycle object.
            ///
            /// Expected continuations include:
            /// - [`EvmBlockComplete::into_parts`]
            /// - [`EvmBlockComplete::discard_context`]
            pub type EvmBlockComplete<C> = $crate::EvmBlockComplete<'static, $ext, $db, C>;

            /// A [`Trevm`] that requires a [`Block`].
            ///
            /// Expected continuations include:
            /// - [`EvmNeedsFirstBlock::open_block`]
            ///
            /// [`Block`]: crate::Block
            pub type EvmNeedsNextBlock = $crate::EvmNeedsNextBlock<'static, $ext, $db>;

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
            pub type EvmErrored<C, E = <C as $crate::BlockContext<$ext, $db>>::Error> =
                $crate::EvmErrored<'static, $ext, $db, C, E>;
        }
    };
}
