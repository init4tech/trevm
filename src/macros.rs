/// Unwraps a Result, returning the value if successful, or returning an errored `Trevm` if not.
#[macro_export]
#[deprecated = "Please use `trevm_tri!` instead"]
macro_rules! unwrap_or_trevm_err {
    ($e:expr, $trevm:expr) => {
        match $e {
            Ok(val) => val,
            Err(e) => return Err($trevm.errored(e.into())),
        }
    };
}

/// Unwraps a Result, returning the value if successful, or returning an errored `Trevm` if not.
#[macro_export]
macro_rules! trevm_try {
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

/// Macro for gas estimation binary search loop.
#[cfg(feature = "estimate_gas")]
macro_rules! estimate_and_adjust {
    ($best:ident, $est:ident, $trevm:ident, $gas_limit:ident, $range:ident) => {
        ::tracing::trace!(
            best = $best.gas_used(),
            max = %$range.max(),
            min = %$range.min(),
            needle = $gas_limit,
            "running gas estimation"
        );
        ($est, $trevm) = $trevm.run_estimate(&$gas_limit.into())?;
        if $est.is_success() {
            $best = $est.clone();
        }
        if let Err(e) = $est.adjust_binary_search_range(&mut $range) {
            ::tracing::trace!(
                %e,
                "error adjusting binary search range"
            );
            return Ok((e, $trevm));
        }
    };
}
