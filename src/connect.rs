use core::convert::Infallible;
use revm::{Database, DatabaseCommit};

/// Trait for types that can be used to connect to a database. Connectors
/// should contain configuration information like filesystem paths. They are
/// intended to enable parallel instantiation of multiple EVMs in multiple
/// threads sharing some database configuration
pub trait DbConnect: Sync {
    /// The database type returned when connecting.
    type Database: Database + DatabaseCommit;

    /// The error type returned when connecting to the database.
    type Error: core::error::Error;

    /// Connect to the database.
    fn connect(&self) -> Result<Self::Database, Self::Error>;
}

impl<Db> DbConnect for Db
where
    Db: Database + DatabaseCommit + Clone + Sync,
{
    type Database = Self;

    type Error = Infallible;

    fn connect(&self) -> Result<Self::Database, Self::Error> {
        Ok(self.clone())
    }
}
