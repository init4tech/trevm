use revm::context::result::ResultAndState;

/// Control flow for transaction execution.
///
/// This enum is used to determine whether to apply or discard the state
/// changes after a transaction is executed.
#[derive(Debug, Clone, Copy)]
pub enum PostflightResult {
    /// Discard the state changes
    Discard(&'static str),
    /// Apply the state changes
    Apply,
}

impl From<bool> for PostflightResult {
    fn from(b: bool) -> Self {
        if b {
            Self::Apply
        } else {
            Self::Discard("")
        }
    }
}

impl From<&'static str> for PostflightResult {
    fn from(s: &'static str) -> Self {
        Self::Discard(s)
    }
}

impl From<Option<&'static str>> for PostflightResult {
    fn from(s: Option<&'static str>) -> Self {
        s.map(Self::Discard).unwrap_or(Self::Apply)
    }
}

impl PostflightResult {
    /// Returns `true` if the result is `Discard`.
    pub const fn is_discard(&self) -> bool {
        matches!(self, Self::Discard(_))
    }

    /// Returns the discard reason if the result is `Discard`.
    pub const fn as_discard_reason(&self) -> Option<&'static str> {
        match self {
            Self::Discard(reason) => Some(reason),
            _ => None,
        }
    }

    /// Returns `true` if the result is `Apply`.
    pub const fn is_apply(&self) -> bool {
        matches!(self, Self::Apply)
    }
}

/// Discard the transaction if the condition is true, providing a discard
/// reason.
#[macro_export]
macro_rules! discard_if {
    ($a:expr, $reason:literal) => {
        if $a {
            tracing::debug!(reason = $reason, "Discarding transaction");
            return $crate::PostflightResult::Discard($reason);
        }
    };
}

/// Inspect the outcome of a transaction execution, and determine whether to
/// apply or discard the state changes.
pub trait PostTx {
    /// Check the result of the EVM execution, potentially mutating self.
    fn run_post_tx(&mut self, result: &ResultAndState) -> PostflightResult;
}

impl<T, O> PostTx for T
where
    T: for<'a> FnMut(&'a ResultAndState) -> O,
    O: Into<PostflightResult>,
{
    fn run_post_tx(&mut self, result: &ResultAndState) -> PostflightResult {
        self(result).into()
    }
}
