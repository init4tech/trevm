use crate::{
    db::{StateAcc, TryStateAcc},
    helpers::Ctx,
    Block, BundleDriver, DriveBundleResult, EvmErrored, EvmNeedsBlock, EvmNeedsTx, EvmReady,
    EvmTransacted, Tx,
};
use alloy::rpc::types::BlockOverrides;
use revm::{
    context::{result::ExecutionResult, ContextTr},
    Database, DatabaseCommit, Inspector,
};

impl<Db, Insp> EvmNeedsTx<Db, Insp>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    /// Close the current block, returning the EVM ready for the next block.
    pub fn close_block(self) -> EvmNeedsBlock<Db, Insp> {
        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { core::mem::transmute(self) }
    }

    /// Drive a bundle to completion, apply some post-bundle logic, and return the
    /// EVM ready for the next bundle or tx.
    pub fn drive_bundle<D>(self, driver: &mut D) -> DriveBundleResult<D, Db, Insp>
    where
        D: BundleDriver<Db, Insp>,
        Db: DatabaseCommit,
    {
        let trevm = driver.run_bundle(self)?;

        match driver.post_bundle(&trevm) {
            Ok(_) => Ok(trevm),
            Err(e) => Err(trevm.errored(e)),
        }
    }

    /// Fill the transaction environment.
    pub fn fill_tx<T: Tx>(mut self, filler: &T) -> EvmReady<Db, Insp> {
        filler.fill_tx(&mut self.inner);
        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { core::mem::transmute(self) }
    }

    /// Execute a transaction. Shortcut for `fill_tx(tx).run()`.
    pub fn run_tx<T: Tx>(
        self,
        filler: &T,
    ) -> Result<EvmTransacted<Db, Insp>, EvmErrored<Db, Insp>> {
        self.fill_tx(filler).run()
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
    pub fn call_tx<T: Tx>(
        self,
        filler: &T,
    ) -> Result<(ExecutionResult, Self), EvmErrored<Db, Insp>> {
        self.fill_tx(filler).call()
    }

    /// Estimate the gas cost of a transaction. Shortcut for `fill_tx(tx).
    /// estimate()`. Returns an [`EstimationResult`] and the EVM populated with
    /// the transaction.
    ///
    /// [`EstimationResult`]: crate::EstimationResult
    #[cfg(feature = "estimate_gas")]
    pub fn estimate_tx_gas<T: Tx>(
        self,
        filler: &T,
    ) -> Result<(crate::EstimationResult, EvmReady<Db, Insp>), EvmErrored<Db, Insp>> {
        self.fill_tx(filler).estimate_gas()
    }
}

impl<Db, Insp> EvmNeedsTx<Db, Insp>
where
    Db: Database + StateAcc,
    Insp: Inspector<Ctx<Db>>,
{
    /// Apply block overrides to the current block.
    ///
    /// Note that this is NOT reversible. The overrides are applied directly to
    /// the underlying state and these changes cannot be removed. If it is
    /// important that you have access to the pre-change state, you should wrap
    /// the existing DB in a new [`State`] and apply the overrides to that.
    ///
    /// [`State`]: revm::database::State
    pub fn apply_block_overrides(mut self, overrides: &BlockOverrides) -> Self {
        overrides.fill_block(&mut self.inner);

        if let Some(hashes) = overrides.block_hash.as_ref() {
            self.inner.db_mut().set_block_hashes(hashes)
        }

        self
    }

    /// Apply block overrides to the current block, if they are provided.
    ///
    /// Note that this is NOT reversible. The overrides are applied directly to
    /// the underlying state and these changes cannot be removed. If it is
    /// important that you have access to the pre-change state, you should wrap
    /// the existing DB in a new [`State`] and apply the overrides to that.
    ///
    /// [`State`]: revm::database::State
    pub fn maybe_apply_block_overrides(self, overrides: Option<&BlockOverrides>) -> Self {
        if let Some(overrides) = overrides {
            self.apply_block_overrides(overrides)
        } else {
            self
        }
    }
}

impl<Db, Insp> EvmNeedsTx<Db, Insp>
where
    Db: Database + TryStateAcc,
    Insp: Inspector<Ctx<Db>>,
{
    /// Apply block overrides to the current block. This function is
    /// intended to be used by shared states, where mutable access may fail, e.
    /// g. an `Arc<Db>`. Prefer [`Self::apply_block_overrides`] when
    /// available.
    ///
    /// Note that this is NOT reversible. The overrides are applied directly to
    /// the underlying state and these changes cannot be removed. If it is
    /// important that you have access to the pre-change state, you should wrap
    /// the existing DB in a new [`State`] and apply the overrides to that.
    ///
    /// [`State`]: revm::database::State
    pub fn try_apply_block_overrides(
        mut self,
        overrides: &BlockOverrides,
    ) -> Result<Self, EvmErrored<Db, Insp, <Db as TryStateAcc>::Error>> {
        overrides.fill_block(&mut self.inner);

        if let Some(hashes) = overrides.block_hash.as_ref() {
            trevm_try!(self.inner.db_mut().try_set_block_hashes(hashes), self);
        }

        Ok(self)
    }

    /// Apply block overrides to the current block, if they are provided. This
    /// function is intended to be used by shared states, where mutable access
    /// may fail, e.g. an `Arc<Db>`.Prefer
    /// [`Self::maybe_apply_block_overrides`] when available.
    ///
    /// Note that this is NOT reversible. The overrides are applied directly to
    /// the underlying state and these changes cannot be removed. If it is
    /// important that you have access to the pre-change state, you should wrap
    /// the existing DB in a new [`State`] and apply the overrides to that.
    ///
    /// [`State`]: revm::database::State
    pub fn try_maybe_apply_block_overrides(
        self,
        overrides: Option<&BlockOverrides>,
    ) -> Result<Self, EvmErrored<Db, Insp, <Db as TryStateAcc>::Error>> {
        if let Some(overrides) = overrides {
            self.try_apply_block_overrides(overrides)
        } else {
            Ok(self)
        }
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
