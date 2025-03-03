use crate::db::ArcUpgradeError;

/// Errors that can occur when working with a concurrent state.
#[derive(Debug, thiserror::Error, Clone, Copy, PartialEq, Eq)]
pub enum ConcurrentStateError {
    /// Failed to upgrade the arc.
    #[error("{0}")]
    Arc(#[from] ArcUpgradeError),

    /// This DB is not the parent of the child.
    #[error("Child belongs to a different parent")]
    NotParent,
}

impl ConcurrentStateError {
    /// Create a new error for when the DB is not the parent of the child.
    pub const fn not_parent() -> Self {
        Self::NotParent
    }

    /// Create a new error for when the arc upgrade fails.
    pub const fn not_unique() -> Self {
        Self::Arc(ArcUpgradeError::NotUnique)
    }
}
