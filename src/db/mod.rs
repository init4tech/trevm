/// Concurrent version of [`revm::database::State`]
#[cfg(feature = "concurrent-db")]
pub mod sync;

/// Database abstraction traits.
mod traits;
pub use traits::{ArcUpgradeError, StateAcc, TryDatabaseCommit, TryStateAcc};
