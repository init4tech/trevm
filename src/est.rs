use revm::{
    context::result::{ExecutionResult, HaltReason, Output},
    primitives::Bytes,
};
use std::ops::Range;

/// Simple wrapper around a range of u64 values, with convenience methods for
/// binary searching.
pub(crate) struct SearchRange(Range<u64>);

impl core::fmt::Display for SearchRange {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}..{}", self.0.start, self.0.end)
    }
}

impl From<Range<u64>> for SearchRange {
    fn from(value: Range<u64>) -> Self {
        Self(value)
    }
}

impl From<SearchRange> for Range<u64> {
    fn from(value: SearchRange) -> Self {
        value.0
    }
}

impl SearchRange {
    /// Create a new search range.
    pub(crate) const fn new(start: u64, end: u64) -> Self {
        Self(start..end)
    }

    /// Calculate the midpoint of the search range.
    pub(crate) const fn midpoint(&self) -> u64 {
        (self.max() + self.min()) / 2
    }

    /// Get the start of the search range.
    pub(crate) const fn min(&self) -> u64 {
        self.0.start
    }

    /// Set the start of the search range.
    pub(crate) const fn set_min(&mut self, min: u64) {
        self.0.start = min;
    }

    /// Raise the minimum of the search range, if the candidate is higher.
    pub(crate) const fn maybe_raise_min(&mut self, candidate: u64) {
        if candidate > self.min() {
            self.set_min(candidate);
        }
    }

    /// Get the end of the search range.
    pub(crate) const fn max(&self) -> u64 {
        self.0.end
    }

    /// Set the end of the search range.
    pub(crate) const fn set_max(&mut self, max: u64) {
        self.0.end = max;
    }

    /// Lower the maximum of the search range, if the candidate is lower.
    pub(crate) const fn maybe_lower_max(&mut self, candidate: u64) {
        if candidate < self.max() {
            self.set_max(candidate);
        }
    }

    /// Calculate the search ratio.
    pub(crate) const fn ratio(&self) -> f64 {
        (self.max() - self.min()) as f64 / self.max() as f64
    }

    /// True if the search range contains the given value.
    pub(crate) fn contains(&self, value: u64) -> bool {
        self.0.contains(&value)
    }

    /// Return the size of the range.
    pub(crate) const fn size(&self) -> u64 {
        self.0.end - self.0.start
    }
}

/// The result of gas estimation.
///
/// This is a trimmed version of [`ExecutionResult`], that contains only
/// information relevant to gas estimation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EstimationResult {
    /// The estimation was successful, the result is the gas estimation.
    Success {
        /// The gas estimation.
        estimation: u64,
        /// The amount of gas that was refunded to the caller as unused.
        refund: u64,
        /// The amount of gas used in the execution.
        gas_used: u64,
        /// The output of execution.
        output: Output,
    },
    /// Estimation failed due to contract revert.
    Revert {
        /// The revert reason.
        reason: Bytes,
        /// The amount of gas used in the execution.
        gas_used: u64,
    },
    /// The estimation failed due to EVM halt.
    Halt {
        /// The halt reason.
        reason: HaltReason,
        /// The amount of gas used in the execution
        gas_used: u64,
    },
}

impl core::fmt::Display for EstimationResult {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Success { estimation, refund, gas_used, .. } => {
                write!(
                    f,
                    "Success {{ estimation: {}, refund: {}, gas_used: {}, .. }}",
                    estimation, refund, gas_used
                )
            }
            Self::Revert { gas_used, .. } => {
                write!(f, "Revert {{ gas_used: {}, .. }}", gas_used)
            }
            Self::Halt { reason, gas_used } => {
                write!(f, "Halt {{ reason: {:?}, gas_used: {} }}", reason, gas_used)
            }
        }
    }
}

impl EstimationResult {
    /// Initialize the estimation result from an execution result and the gas
    /// limit of the transaction that produced the estimation.
    pub fn from_limit_and_execution_result(limit: u64, value: &ExecutionResult) -> Self {
        match value {
            ExecutionResult::Success { gas_used, output, gas_refunded, .. } => Self::Success {
                estimation: limit,
                refund: *gas_refunded,
                gas_used: *gas_used,
                output: output.clone(),
            },
            ExecutionResult::Revert { output, gas_used } => {
                Self::Revert { reason: output.clone(), gas_used: *gas_used }
            }
            ExecutionResult::Halt { reason, gas_used } => {
                Self::Halt { reason: *reason, gas_used: *gas_used }
            }
        }
    }

    /// Create a successful estimation result with a gas estimation of 21000.
    pub const fn basic_transfer_success(estimation: u64) -> Self {
        Self::Success {
            estimation,
            refund: 0,
            gas_used: estimation,
            output: Output::Call(Bytes::new()),
        }
    }

    /// Return true if the execution was successful.
    pub const fn is_success(&self) -> bool {
        matches!(self, Self::Success { .. })
    }

    /// Return true if the execution was not successful.
    pub const fn is_failure(&self) -> bool {
        !self.is_success()
    }

    /// Get the gas estimation, if the execution was successful.
    pub const fn gas_estimation(&self) -> Option<u64> {
        match self {
            Self::Success { estimation, .. } => Some(*estimation),
            _ => None,
        }
    }

    /// Get the gas refunded, if the execution was successful.
    pub const fn gas_refunded(&self) -> Option<u64> {
        match self {
            Self::Success { refund, .. } => Some(*refund),
            _ => None,
        }
    }

    /// Get the output, if the execution was successful.
    pub const fn output(&self) -> Option<&Output> {
        match self {
            Self::Success { output, .. } => Some(output),
            _ => None,
        }
    }

    /// Get the gas used in execution, regardless of the outcome.
    pub const fn gas_used(&self) -> u64 {
        match self {
            Self::Success { gas_used, .. } => *gas_used,
            Self::Revert { gas_used, .. } => *gas_used,
            Self::Halt { gas_used, .. } => *gas_used,
        }
    }

    /// Return true if the execution failed due to revert.
    pub const fn is_revert(&self) -> bool {
        matches!(self, Self::Revert { .. })
    }

    /// Get the revert reason if the execution failed due to revert.
    pub const fn revert_reason(&self) -> Option<&Bytes> {
        match self {
            Self::Revert { reason, .. } => Some(reason),
            _ => None,
        }
    }

    /// Return true if the execution failed due to EVM halt.
    pub const fn is_halt(&self) -> bool {
        matches!(self, Self::Halt { .. })
    }

    /// Get the halt reason if the execution failed due to EVM halt.
    pub const fn halt_reason(&self) -> Option<&HaltReason> {
        match self {
            Self::Halt { reason, .. } => Some(reason),
            _ => None,
        }
    }

    /// Adjust the binary search range based on the estimation outcome.
    pub(crate) fn adjust_binary_search_range(
        &self,
        limit: u64,
        range: &mut SearchRange,
    ) -> Result<(), Self> {
        match self {
            Self::Success { .. } => range.set_max(limit),
            Self::Revert { .. } => range.set_min(limit),
            Self::Halt { reason, gas_used } => {
                // Both `OutOfGas` and `InvalidEFOpcode` can occur dynamically
                // if the gas left is too low. Treat this as an out of gas
                // condition, knowing that the call succeeds with a
                // higher gas limit.
                //
                // Common usage of invalid opcode in OpenZeppelin:
                // <https://github.com/OpenZeppelin/openzeppelin-contracts/blob/94697be8a3f0dfcd95dfb13ffbd39b5973f5c65d/contracts/metatx/ERC2771Forwarder.sol#L360-L367>
                if matches!(reason, HaltReason::OutOfGas(_) | HaltReason::InvalidFEOpcode) {
                    range.set_min(limit);
                } else {
                    return Err(Self::Halt { reason: *reason, gas_used: *gas_used });
                }
            }
        }
        Ok(())
    }
}

// Some code above is reproduced from `reth`. It is reused here under the MIT
// license.
//
// The MIT License (MIT)
//
// Copyright (c) 2022-2024 Reth Contributors
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.
