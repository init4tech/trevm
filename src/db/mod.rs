/// Concurrent version of [`revm::database::State`]
#[cfg(feature = "concurrent-db")]
pub mod sync;

/// Database abstraction traits.
mod traits;
pub use traits::{ArcUpgradeError, StateAcc, TryDatabaseCommit, TryStateAcc};

/// Cache-on-write database. A memory cache that caches only on write, not on
/// read. Intended to wrap some other caching database.
pub mod cow;
