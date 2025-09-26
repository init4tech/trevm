use crate::{
    db::DbConnect, helpers::Ctx, Block, Cfg, EvmErrored, EvmNeedsBlock, EvmNeedsCfg, EvmNeedsTx,
    EvmReady, EvmTransacted, Tx,
};
use revm::{
    context::result::{EVMError, ResultAndState},
    Database, Inspector,
};
use std::format;

/// Trait for types that can create EVM instances.
///
/// Factories should contain configuration information like `Insp` types, and
/// database connections. They are intended to enable parallel instantiation
/// of multiple EVMs in multiple threads sharing some configuration or backing
/// store.
///
/// The lifetime on this trait allows the resulting EVM to borrow from the
/// connector. E.g. the connector may contain some `Db` and the resulting EVM
/// may contain `&Db`. This allows for (e.g.) shared caches between EVMs on
/// multiple threads.
pub trait EvmFactory: DbConnect {
    /// The `Insp` type used in the resulting EVM.
    ///
    /// Recommend using [`NoOpInspector`] for most use cases.
    ///
    /// [`NoOpInspector`]: revm::inspector::NoOpInspector
    type Insp: Sync + Inspector<Ctx<Self::Database>>;

    /// Create a new EVM instance with the given database connection and
    /// extension.
    fn create(&self) -> Result<EvmNeedsCfg<Self::Database, Self::Insp>, Self::Error>;

    /// Create a new EVM instance and parameterize it with a [`Cfg`].
    fn create_with_cfg<C>(
        &self,
        cfg: &C,
    ) -> Result<EvmNeedsBlock<Self::Database, Self::Insp>, Self::Error>
    where
        C: Cfg,
    {
        self.create().map(|evm| evm.fill_cfg(cfg))
    }

    /// Create a new EVM instance and parameterize it with a [`Cfg`] and a
    /// [`Block`].
    fn create_with_block<C, B>(
        &self,
        cfg: &C,
        block: &B,
    ) -> Result<EvmNeedsTx<Self::Database, Self::Insp>, Self::Error>
    where
        C: Cfg,
        B: Block,
    {
        self.create_with_cfg(cfg).map(|evm| evm.fill_block(block))
    }

    /// Create a new EVM instance, and parameterize it with a [`Cfg`], a
    /// [`Block`], and a [`Tx`], yielding an [`EvmReady`].
    fn create_with_tx<C, B, T>(
        &self,
        cfg: &C,
        block: &B,
        tx: &T,
    ) -> Result<EvmReady<Self::Database, Self::Insp>, Self::Error>
    where
        C: Cfg,
        B: Block,
        T: Tx,
    {
        self.create_with_block(cfg, block).map(|evm| evm.fill_tx(tx))
    }

    /// Create a new EVM instance, parameterize it with a [`Cfg`], a
    /// [`Block`], and a [`Tx`], and run the transaction, yielding either
    /// [`EvmTransacted`] or [`EvmErrored`].
    #[allow(clippy::type_complexity)]
    fn transact<C, B, T>(
        &self,
        cfg: &C,
        block: &B,
        tx: &T,
    ) -> Result<
        Result<EvmTransacted<Self::Database, Self::Insp>, EvmErrored<Self::Database, Self::Insp>>,
        Self::Error,
    >
    where
        C: Cfg,
        B: Block,
        T: Tx,
    {
        let evm = self.create_with_tx(cfg, block, tx)?;
        Ok(evm.run())
    }

    /// Run a transaction, take the [`ResultAndState`], and discard the Evm.
    /// This is a high-level shortcut function.
    fn run<C, B, T>(
        &self,
        cfg: &C,
        block: &B,
        tx: &T,
    ) -> Result<ResultAndState, EVMError<<Self::Database as Database>::Error>>
    where
        C: Cfg,
        B: Block,
        T: Tx,
    {
        let trevm = self.transact(cfg, block, tx).map_err(|e| EVMError::Custom(format!("{e}")))?;

        match trevm {
            Ok(t) => Ok(t.into_result_and_state()),
            Err(t) => Err(t.into_error()),
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
