/// Concurrent version of [`revm::database::State`]
#[cfg(feature = "concurrent-db")]
pub mod sync;

/// Database abstraction traits.
mod traits;
pub use traits::{ArcUpgradeError, CachingDb, StateAcc, TryCachingDb, TryStateAcc};

/// Cache-on-write database. A memory cache that caches only on write, not on
/// read. Intended to wrap some other caching database.
pub mod cow;

#[cfg(feature = "alloydb")]
/// Alloy-powered revm Database implementation that fetches data over the network.
pub mod alloy;
