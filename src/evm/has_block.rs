use crate::{helpers::Ctx, Block, EvmErrored, HasBlock, Trevm};
use alloy::primitives::{Address, U256};
use revm::{
    context::{Block as _, BlockEnv, ContextSetters, ContextTr},
    Database, Inspector,
};

impl<Db, Insp, TrevmState> Trevm<Db, Insp, TrevmState>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
    TrevmState: HasBlock,
{
    /// Get a reference to the current block environment.
    pub fn block(&self) -> &BlockEnv {
        self.inner.block()
    }

    /// Get the current block gas limit.
    pub fn block_gas_limit(&self) -> u64 {
        self.block().gas_limit()
    }

    /// Get the current block number.
    pub fn block_number(&self) -> U256 {
        self.block().number()
    }

    /// Get the current block timestamp.
    pub fn block_timestamp(&self) -> U256 {
        self.block().timestamp()
    }

    /// Get the block beneficiary address.
    pub fn beneficiary(&self) -> Address {
        self.block().beneficiary()
    }

    /// Run a function with the provided block, then restore the previous block.
    pub fn with_block<B, F, NewState>(mut self, b: &B, f: F) -> Trevm<Db, Insp, NewState>
    where
        B: Block,
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
        NewState: HasBlock,
    {
        let previous = self.inner.block().clone();
        b.fill_block(&mut self.inner);

        let mut this = f(self);
        this.inner.ctx.set_block(previous);
        this
    }

    /// Run a fallible function with the provided block, then restore the previous block.
    pub fn try_with_block<B, F, NewState, E>(
        mut self,
        b: &B,
        f: F,
    ) -> Result<Trevm<Db, Insp, NewState>, EvmErrored<Db, Insp, E>>
    where
        F: FnOnce(Self) -> Result<Trevm<Db, Insp, NewState>, EvmErrored<Db, Insp, E>>,
        B: Block,
        NewState: HasBlock,
    {
        let previous = self.inner.block().clone();
        b.fill_block(&mut self.inner);

        match f(self) {
            Ok(mut evm) => {
                evm.inner.ctx.set_block(previous);
                Ok(evm)
            }
            Err(mut evm) => {
                evm.inner.ctx.set_block(previous);
                Err(evm)
            }
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
