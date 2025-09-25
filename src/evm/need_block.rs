use crate::{
    db::{StateAcc, TryStateAcc},
    driver::DriveBlockResult,
    helpers::Ctx,
    Block, BlockDriver, ChainDriver, DriveChainResult, EvmErrored, EvmNeedsBlock, EvmNeedsTx,
};
use revm::{
    context::ContextTr,
    database::{states::bundle_state::BundleRetention, BundleState},
    Database, DatabaseCommit, Inspector,
};

impl<Db, Insp> EvmNeedsBlock<Db, Insp>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    /// Open a block, apply some logic, and return the EVM ready for the next
    /// block.
    pub fn drive_block<D>(self, driver: &mut D) -> DriveBlockResult<D, Db, Insp>
    where
        D: BlockDriver<Db, Insp>,
        Db: DatabaseCommit,
    {
        let trevm = self.fill_block(driver.block());
        let trevm = driver.run_txns(trevm)?;

        let trevm = trevm.close_block();

        match driver.post_block(&trevm) {
            Ok(_) => Ok(trevm),
            Err(e) => Err(trevm.errored(e)),
        }
    }

    /// Drive trevm through a set of blocks.
    ///
    /// # Panics
    ///
    /// If the driver contains no blocks.
    pub fn drive_chain<D>(self, driver: &mut D) -> DriveChainResult<D, Db, Insp>
    where
        D: ChainDriver<Db, Insp>,
        Db: DatabaseCommit,
    {
        let block_count = driver.blocks().len();

        let mut trevm = self
            .drive_block(&mut driver.blocks()[0])
            .map_err(EvmErrored::err_into::<<D as ChainDriver<Db, Insp>>::Error>)?;

        if let Err(e) = driver.interblock(&trevm, 0) {
            return Err(trevm.errored(e));
        }

        for i in 1..block_count {
            trevm = {
                let trevm = trevm
                    .drive_block(&mut driver.blocks()[i])
                    .map_err(EvmErrored::err_into::<<D as ChainDriver<Db, Insp>>::Error>)?;
                if let Err(e) = driver.interblock(&trevm, i) {
                    return Err(trevm.errored(e));
                }
                trevm
            };
        }
        Ok(trevm)
    }

    /// Fill a block and return the EVM ready for a transaction.
    ///
    /// This does not perform any pre- or post-block logic. To manage block
    /// lifecycles, use [`Self::drive_block`] or [`Self::drive_chain`] instead.
    pub fn fill_block<B: Block>(mut self, filler: &B) -> EvmNeedsTx<Db, Insp> {
        filler.fill_block(self.inner_mut_unchecked());
        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { core::mem::transmute(self) }
    }
}

impl<Db, Insp> EvmNeedsBlock<Db, Insp>
where
    Db: Database + StateAcc,
    Insp: Inspector<Ctx<Db>>,
{
    /// Finish execution and return the outputs.
    ///
    /// If the State has not been built with
    /// [revm::database::StateBuilder::with_bundle_update] then the returned
    /// [`BundleState`] will be meaningless.
    ///
    /// See [`State::merge_transitions`] and [`State::take_bundle`].
    ///
    /// [`State::merge_transitions`]: revm::database::State::merge_transitions
    /// [`State::take_bundle`]: revm::database::State::take_bundle
    pub fn finish(self) -> BundleState {
        let Self { inner: mut evm, .. } = self;
        evm.db_mut().merge_transitions(BundleRetention::Reverts);
        let bundle = evm.db_mut().take_bundle();

        bundle
    }
}

impl<Db, Insp> EvmNeedsBlock<Db, Insp>
where
    Db: Database + TryStateAcc,
    Insp: Inspector<Ctx<Db>>,
{
    /// Fallibly finish execution and return the outputs. This function is
    /// intended to be used by shared states, where mutable access may fail, e.
    /// g. an `Arc<Db>`. Prefer [`Self::finish`] when available.
    ///
    /// If the State has not been built with
    /// [revm::database::StateBuilder::with_bundle_update] then the returned
    /// [`BundleState`] will be meaningless.
    ///
    /// See [`State::merge_transitions`] and [`State::take_bundle`].
    ///
    /// [`State::merge_transitions`]: revm::database::State::merge_transitions
    /// [`State::take_bundle`]: revm::database::State::take_bundle
    pub fn try_finish(
        mut self,
    ) -> Result<BundleState, EvmErrored<Db, Insp, <Db as TryStateAcc>::Error>> {
        let db = self.inner.db_mut();

        trevm_try!(db.try_merge_transitions(BundleRetention::Reverts), self);

        let bundle = trevm_try!(db.try_take_bundle(), self);

        Ok(bundle)
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
