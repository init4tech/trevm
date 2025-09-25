use crate::{
    helpers::Ctx, ErroredState, EvmErrored, EvmNeedsTx, EvmReady, EvmTransacted, TransactedState,
    Trevm,
};
use revm::{
    context::result::{EVMError, ExecutionResult},
    interpreter::gas::calculate_initial_tx_gas_for_tx,
    Database, InspectEvm, Inspector,
};

impl<Db, Insp> EvmReady<Db, Insp>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    /// Clear the current transaction environment.
    pub fn clear_tx(self) -> EvmNeedsTx<Db, Insp> {
        // NB: we do not clear the tx env here, as we may read it during post-tx
        // logic in a block driver

        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { core::mem::transmute(self) }
    }

    /// Execute the loaded transaction. This is a wrapper around
    /// [`InspectEvm::inspect_tx`] and produces either [`EvmTransacted`] or
    /// [`EvmErrored`].
    pub fn run(mut self) -> Result<EvmTransacted<Db, Insp>, EvmErrored<Db, Insp>> {
        let result = self.inner.inspect_tx(self.tx().clone());

        let Self { inner, .. } = self;

        match result {
            Ok(result) => Ok(Trevm { inner, state: TransactedState { result } }),
            Err(error) => Err(EvmErrored { inner, state: ErroredState { error } }),
        }
    }

    /// Simulate the transaction, and return the [`ExecutionResult`]. The
    /// following modifications are made to the environment while simulating.
    ///
    /// - [EIP-3607] is disabled.
    /// - Base fee checks are disabled.
    /// - Nonce checks are disabled.
    ///
    /// [EIP-3607]: https://eips.ethereum.org/EIPS/eip-3607
    #[cfg(feature = "call")]
    pub fn call(self) -> Result<(ExecutionResult, EvmNeedsTx<Db, Insp>), EvmErrored<Db, Insp>> {
        let mut output = std::mem::MaybeUninit::uninit();

        let gas_limit = self.tx().gas_limit;

        let this =
            self.try_with_call_filler(&crate::fillers::CallFiller { gas_limit }, |this| {
                let t = this.run()?;

                let (o, t) = t.take_result();

                output.write(o);

                Ok(t)
            })?;
        Ok((unsafe { output.assume_init() }, this))
    }

    /// Calculate the minimum gas required to start EVM execution.
    ///
    /// This uses [`calculate_initial_tx_gas_for_tx`] to calculate the initial
    /// gas. Its output is dependent on
    /// - the EVM spec
    /// - the input data
    /// - whether the transaction is a contract creation or a call
    /// - the EIP-2930 access list
    /// - the number of [EIP-7702] authorizations
    ///
    /// [EIP-2930]: https://eips.ethereum.org/EIPS/eip-2930
    /// [EIP-7702]: https://eips.ethereum.org/EIPS/eip-7702
    pub fn calculate_initial_gas(&self) -> u64 {
        calculate_initial_tx_gas_for_tx(self.tx(), self.spec_id()).initial_gas
    }

    /// Estimate gas for a simple transfer. This will
    /// - Check that the transaction has no input data.
    /// - Check that the target is not a `create`.
    /// - Check that the target is not a contract.
    /// - Return the minimum gas required for the transfer.
    #[cfg(feature = "estimate_gas")]
    fn estimate_gas_simple_transfer(
        &mut self,
    ) -> Result<Option<u64>, EVMError<<Db as Database>::Error>> {
        use alloy::consensus::constants::KECCAK_EMPTY;
        use tracing::trace;

        if !self.is_transfer() {
            return Ok(None);
        }

        // Shortcut if the tx is create, otherwise read the account
        let Some(acc) = self.callee_account()? else { return Ok(None) };

        // If the code hash is not empty, then the target is a contract
        if acc.code_hash != KECCAK_EMPTY {
            return Ok(None);
        }

        // delegate calculation to revm. This ensures that things like bogus
        // 2930 access lists don't mess up our estimates
        let initial = self.calculate_initial_gas();
        trace!(initial, "using initial gas for simple transfer");
        Ok(Some(initial))
    }

    /// Convenience function to simplify nesting of [`Self::estimate_gas`].
    #[cfg(feature = "estimate_gas")]
    fn run_estimate(
        self,
        filler: &crate::fillers::GasEstimationFiller,
    ) -> Result<(crate::EstimationResult, Self), EvmErrored<Db, Insp>> {
        use tracing::trace;

        let mut estimation = std::mem::MaybeUninit::uninit();

        let this = self.try_with_estimate_gas_filler(filler, |this| match this.run() {
            Ok(trevm) => {
                let (e, t) = trevm.take_estimation();

                estimation.write(e);
                Ok(t)
            }
            Err(err) => Err(err),
        })?;

        // SAFETY: if we did not shortcut return, then estimation was
        // definitely written
        Ok((unsafe { estimation.assume_init() }, this))
            .inspect(|(est, _)| trace!(?est, "gas estimation result",))
    }

    /// Implements gas estimation. This will output an estimate of the minimum
    /// amount of gas that the transaction will consume, calculated via
    /// iterated simulation.
    ///
    /// In the worst case this will perform a binary search, resulting in
    /// `O(log(n))` simulations.
    ///
    /// ## Returns
    ///
    /// An [`EstimationResult`] and the EVM with the transaction populated.
    /// Like with the remainder of the API, an EVM revert or an EVM halt is
    /// NOT an error. An [`Err`] is returned only if the EVM encounters a
    /// condition of use violation or a DB access fails.
    ///
    /// ## Estimation Algorithm
    ///
    /// This function is largely based on the reth RPC estimation algorithm,
    /// which can be found [here]. The algorithm is as follows:
    ///
    /// - Disable eip-3607, allowing estimation from contract accounts.
    /// - Disable base fee checks.
    /// - Check if the transaction is a simple transfer
    ///     - Is there input data empty? If yes, proceed to regular estimation
    ///     - Is the callee a contract? If yes, proceed to regular estimation
    ///     - Otherwise, shortcut return success with [`MIN_TRANSACTION_GAS`].
    /// - Simulate the transaction with the maximum possible gas limit.
    ///     - If the simulation fails, shortcut return the failure.
    ///     - If succesful, store the gas used as the search minimum.
    /// - Simulate the transaction with an "optimistic" gas limit.
    ///     - If the simulation fails, shortcut return the failure.
    ///     - If succesful, begin the binary search around that range.
    /// - Binary search loop:
    ///     - If the search range is small enough, break the loop and return
    ///       the current estimate.
    ///     - Calculate a new gas limit based on the midpoint of the search
    ///       range.
    ///     - Simulate the transaction with the new gas limit.
    ///     - Adjust the search range based on the simulation result:
    ///         - If the result is a success, pull the search max down to the
    ///           limit.
    ///         - If the result is a revert, push the search min up to the
    ///           limit.
    ///         - If the result is a halt, check if the halt is potentially a
    ///           gas-dynamic halt.
    ///             - If it is, treat it as a revert.
    ///             - If it is not, shortcut return the halt.
    ///     - Loop.
    ///
    /// [here]: https://github.com/paradigmxyz/reth/blob/ad503a08fa242b28ad3c1fea9caa83df2dfcf72d/crates/rpc/rpc-eth-api/src/helpers/estimate.rs#L35-L42
    /// [`EstimationREsult`]: crate::EstimationResult
    /// [`MIN_TRANSACTION_GAS`]: crate::MIN_TRANSACTION_GAS
    #[cfg(feature = "estimate_gas")]
    pub fn estimate_gas(mut self) -> Result<(crate::EstimationResult, Self), EvmErrored<Db, Insp>> {
        use tracing::{debug, enabled, trace};

        if let Some(est) = trevm_try!(self.estimate_gas_simple_transfer(), self) {
            return Ok((crate::EstimationResult::basic_transfer_success(est), self));
        }

        // We shrink the gas limit to 64 bits, as using more than 18 quintillion
        // gas in a block is unlikely.
        let initial_limit = self.gas_limit();

        // Start the search range at 21_000 gas.
        let mut search_range =
            crate::est::SearchRange::new(crate::MIN_TRANSACTION_GAS, initial_limit);

        let span = tracing::debug_span!(
            "Trevm::estimate_gas",
            start_min = search_range.min(),
            start_max = search_range.max(),
        );
        if enabled!(tracing::Level::TRACE) {
            span.record("tx", format!("{:?}", &self.tx()));
            span.record("block", format!("{:?}", &self.block()));
        } else {
            span.record("tx", "omitted. Use TRACE for details");
        }
        let _e = span.enter();

        // Cap the gas limit to the caller's allowance and block limit
        trevm_try!(self.cap_tx_gas(), self);
        search_range.maybe_lower_max(self.gas_limit());

        // Raise the floor to the amount of gas required to initialize the EVM.
        search_range.maybe_raise_min(self.calculate_initial_gas());

        // Run an estimate with the max gas limit.
        // NB: we declare these mut as we re-use the binding throughout the
        // function.
        debug!(gas_limit = self.gas_limit(), "running optimistic estimate");
        let (mut estimate, mut trevm) = self.run_estimate(&search_range.max().into())?;

        // If it failed, no amount of gas is likely to work, so we shortcut
        // return.
        if estimate.is_failure() {
            debug!(%estimate, "optimistic estimate failed");
            return Ok((estimate, trevm));
        }
        trace!(%estimate, "optimistic estimate succeeded");

        // Now we know that it succeeds at _some_ gas limit. We can now binary
        // search. We start by recording the initial best estimate. We'll update
        // this best-estimate as we go inside the `estimate_and_adjust` macro
        // invocations.
        let mut best = estimate.clone();
        let mut gas_used = estimate.gas_used();
        let gas_refunded = estimate.gas_refunded().expect("checked is_failure");

        // NB: if we've made it this far it's very unlikely that `gas_used` is
        // less than 21_000, but we'll check anyway.
        search_range.maybe_raise_min(gas_used - 1);

        // NB: This is a heuristic adopted from geth and reth
        // The goal is to check if the first-run is actually very close to the
        // real estimate, thereby cutting down on the number of iterations in
        // the later search loop.
        // https://github.com/ethereum/go-ethereum/blob/a5a4fa7032bb248f5a7c40f4e8df2b131c4186a4/eth/gasestimator/gasestimator.go#L132-L135
        // NB: 64 / 63 is due to Ethereum's gas-forwarding rules. Each call
        // frame can forward only 63/64 of the gas it has when it makes a new
        // frame.
        let mut needle = (gas_used + gas_refunded + revm::interpreter::gas::CALL_STIPEND) * 64 / 63;

        // If the first search is outside the range, we don't need to try it.
        if search_range.contains(needle) {
            estimate_and_adjust!(best, estimate, trevm, needle, search_range);
            // NB: `estimate` is rebound in the macro, so do not move this line
            // up.
            gas_used = estimate.gas_used();
        }

        // NB: This is a heuristic adopted from reth.
        // Pick a point that's close to the estimated gas
        needle = std::cmp::min(gas_used * 3, search_range.midpoint());

        // Binary search loop.
        // The second conditional is a heuristic adopted from geth and reth.
        // An estimation error is allowed once the current gas limit range
        // used in the binary search is small enough (less than 1.5% of the
        // highest gas limit)
        // <https://github.com/ethereum/go-ethereum/blob/a5a4fa7032bb248f5a7c40f4e8df2b131c4186
        while search_range.size() > 1 && search_range.ratio() > 0.015 {
            estimate_and_adjust!(best, estimate, trevm, needle, search_range);
            needle = search_range.midpoint();
        }

        Ok((best, trevm))
    }
}

// Some code above and documentation is adapted from the revm crate, and is
// reproduced here under the terms of the MIT license.
//
// MIT License
//
// Copyright (c) 2021-2024 draganrakita
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

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
