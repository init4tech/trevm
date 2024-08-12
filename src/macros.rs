/// Unwraps a Result, returning the value if successful, or returning an errored `Trevm` if not.
#[macro_export]
macro_rules! unwrap_or_trevm_err {
    ($e:expr, $trevm:expr) => {
        match $e {
            Ok(val) => val,
            Err(e) => return Err($trevm.errored(e.into())),
        }
    };
}

/// Executes a condition, returning an errored `Trevm` if not successful.
#[macro_export]
macro_rules! trevm_ensure {
    ($cond:expr, $trevm:expr, $err:expr) => {
        if !$cond {
            trevm_bail!($trevm, $err);
        }
    };
}

/// Returns an errored `Trevm` with the provided error.
#[macro_export]
macro_rules! trevm_bail {
    ($trevm:expr, $err:expr) => {
        return Err($trevm.errored($err))
    };
}
