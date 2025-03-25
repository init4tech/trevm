use crate::{
    Block, Cfg, EvmErrored, EvmNeedsBlock, EvmNeedsCfg, EvmNeedsTx, EvmReady, EvmTransacted, Tx,
};
use core::convert::Infallible;
use revm::{
    context::result::{EVMError, ResultAndState},
    Database,
};
use std::format;

/// Trait for types that can be used to connect to a database.
///
/// Connectors should contain configuration information like filesystem paths.
/// They are intended to enable parallel instantiation of multiple EVMs in
/// multiple threads sharing some database configuration
///
/// The lifetime on this trait allows the resulting DB to borrow from the
/// connector. E.g. the connector may contain some `Db` and the resulting Db may
/// contain `&Db`. This allows for (e.g.) shared caches between DBs on multiple
/// threads.
pub trait DbConnect: Sync {
    /// The database type returned when connecting.
    type Database: Database;

    /// The error type returned when connecting to the database.
    type Error: core::error::Error;

    /// Connect to the database.
    fn connect(&self) -> Result<Self::Database, Self::Error>;
}

impl<Db> DbConnect for Db
where
    Db: Database + Clone + Sync,
{
    type Database = Self;

    type Error = Infallible;

    fn connect(&self) -> Result<Self::Database, Self::Error> {
        Ok(self.clone())
    }
}

/// Trait for types that can create EVM instances.
///
/// Factories should contain configuration information like chain `EXT` types,
/// and database connections. They are intended to enable parallel instantiation
/// of multiple EVMs in multiple threads sharing some configuration or backing
/// store.
///
/// The lifetime on this trait allows the resulting EVM to borrow from the
/// connector. E.g. the connector may contain some `Db` and the resulting EVM
/// may contain `&Db`. This allows for (e.g.) shared caches between EVMs on
/// multiple threads.
pub trait EvmFactory: DbConnect {
    /// The `Insp` type used in the resulting EVM.
    type Insp: Sync;

    /// Create a new EVM instance with the given database connection and
    /// extension.
    fn create(&self) -> Result<EvmNeedsCfg<Self::Database, Self::Insp>, Self::Error>;

    /// Create a new EVM instance and parameterize it with a [`Cfg`].
    fn create_with_cfg<C>(
        &self,
        cfg: &C,
    ) -> Result<EvmNeedsBlock<Self::Database, Self::Insp>, Self::Error>
    where
        C: Cfg,
    {
        self.create().map(|evm| evm.fill_cfg(cfg))
    }

    /// Create a new EVM instance and parameterize it with a [`Cfg`] and a
    /// [`Block`].
    fn create_with_block<C, B>(
        &self,
        cfg: &C,
        block: &B,
    ) -> Result<EvmNeedsTx<Self::Database, Self::Insp>, Self::Error>
    where
        C: Cfg,
        B: Block,
    {
        self.create_with_cfg(cfg).map(|evm| evm.fill_block(block))
    }

    /// Create a new EVM instance, and parameterize it with a [`Cfg`], a
    /// [`Block`], and a [`Tx`], yielding an [`EvmReady`].
    fn create_with_tx<C, B, T>(
        &self,
        cfg: &C,
        block: &B,
        tx: &T,
    ) -> Result<EvmReady<Self::Database, Self::Insp>, Self::Error>
    where
        C: Cfg,
        B: Block,
        T: Tx,
    {
        self.create_with_block(cfg, block).map(|evm| evm.fill_tx(tx))
    }

    /// Create a new EVM instance, parameterize it with a [`Cfg`], a
    /// [`Block`], and a [`Tx`], and run the transaction, yielding either
    /// [`EvmTransacted`] or [`EvmErrored`].
    #[allow(clippy::type_complexity)]
    fn transact<C, B, T>(
        &self,
        cfg: &C,
        block: &B,
        tx: &T,
    ) -> Result<
        Result<EvmTransacted<Self::Database, Self::Insp>, EvmErrored<Self::Database, Self::Insp>>,
        Self::Error,
    >
    where
        C: Cfg,
        B: Block,
        T: Tx,
    {
        let evm = self.create_with_tx(cfg, block, tx)?;
        Ok(evm.run())
    }

    /// Run a transaction, take the [`ResultAndState`], and discard the Evm.
    /// This is a high-level shortcut function.
    fn run<C, B, T>(
        &self,
        cfg: &C,
        block: &B,
        tx: &T,
    ) -> Result<ResultAndState, EVMError<<Self::Database as Database>::Error>>
    where
        C: Cfg,
        B: Block,
        T: Tx,
    {
        let trevm = self.transact(cfg, block, tx).map_err(|e| EVMError::Custom(format!("{e}")))?;

        match trevm {
            Ok(t) => Ok(t.into_result_and_state()),
            Err(t) => Err(t.into_error()),
        }
    }
}
