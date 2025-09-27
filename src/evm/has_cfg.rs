use crate::{helpers::Ctx, Cfg, EvmErrored, HasCfg, Trevm};
use revm::{context::ContextTr, Database, Inspector};

impl<Db, Insp, TrevmState> Trevm<Db, Insp, TrevmState>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
    TrevmState: HasCfg,
{
    /// Set the [EIP-170] contract code size limit. By default this is set to
    /// 0x6000 bytes (~25KiB). Contracts whose bytecode is larger than this
    /// limit cannot be deployed and will produce a [`CreateInitCodeSizeLimit`]
    /// error.
    ///
    /// [`CreateInitCodeSizeLimit`]: revm::context::result::InvalidTransaction::CreateInitCodeSizeLimit
    /// [`Eip-170`]: https://eips.ethereum.org/EIPS/eip-170
    pub fn set_code_size_limit(&mut self, limit: usize) -> Option<usize> {
        let mut csl = None;
        self.inner.ctx.modify_cfg(|cfg| {
            csl = cfg.limit_contract_code_size.replace(limit);
        });
        csl
    }

    /// Disable the [EIP-170] contract code size limit, returning the previous
    /// setting.
    ///
    /// [`Eip-170`]: https://eips.ethereum.org/EIPS/eip-170
    pub fn disable_code_size_limit(&mut self) -> Option<usize> {
        let mut csl = None;
        self.inner.ctx.modify_cfg(|cfg| csl = cfg.limit_contract_code_size.take());
        csl
    }

    /// Run a closure with the code size limit disabled, then restore the
    /// previous setting.
    pub fn without_code_size_limit<F, NewState: HasCfg>(mut self, f: F) -> Trevm<Db, Insp, NewState>
    where
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
    {
        let limit = self.disable_code_size_limit();
        let mut new = f(self);
        if let Some(limit) = limit {
            new.set_code_size_limit(limit);
        }
        new
    }

    /// Set the [EIP-170] contract code size limit to the default value of
    /// 0x6000 bytes (~25KiB), returning the previous setting. Contracts whose
    /// bytecode is larger than this limit cannot be deployed and will produce
    /// a [`CreateInitCodeSizeLimit`] error.
    ///
    /// [`CreateInitCodeSizeLimit`]: revm::context::result::InvalidTransaction::CreateInitCodeSizeLimit
    /// [`Eip-170`]: https://eips.ethereum.org/EIPS/eip-170
    pub fn set_default_code_size_limit(&mut self) -> Option<usize> {
        self.set_code_size_limit(0x6000)
    }

    /// Disable the [EIP-155] chain ID check.
    ///
    /// [`EIP-155`]: https://eips.ethereum.org/EIPS/eip-155
    pub fn disable_chain_id_check(&mut self) {
        self.inner.ctx.modify_cfg(|cfg| cfg.tx_chain_id_check = false);
    }

    /// Enable the [EIP-155] chain ID check.
    ///
    /// [`EIP-155`]: https://eips.ethereum.org/EIPS/eip-155
    pub fn enable_chain_id_check(&mut self) {
        self.inner.ctx.modify_cfg(|cfg| cfg.tx_chain_id_check = true);
    }

    /// Run a closure with the chain ID check disabled, then restore the previous
    /// setting.
    ///
    /// [`EIP-155`]: https://eips.ethereum.org/EIPS/eip-155
    pub fn without_chain_id_check<F, NewState: HasCfg>(mut self, f: F) -> Trevm<Db, Insp, NewState>
    where
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
    {
        let previous = self.inner.cfg().tx_chain_id_check;
        self.disable_chain_id_check();
        let mut new = f(self);
        new.inner.ctx.modify_cfg(|cfg| cfg.tx_chain_id_check = previous);
        new
    }

    /// Run a function with the provided configuration, then restore the
    /// previous configuration. This will not affect the block and tx, if those
    /// have been filled.
    pub fn with_cfg<C, F, NewState>(mut self, cfg: &C, f: F) -> Trevm<Db, Insp, NewState>
    where
        C: Cfg,
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
        NewState: HasCfg,
    {
        let previous = self.inner.cfg().clone();
        cfg.fill_cfg(&mut self.inner);

        let mut this = f(self);
        this.inner.ctx.modify_cfg(|cfg| *cfg = previous);
        this
    }

    /// Run a fallible function with the provided configuration, then restore the
    /// previous configuration. This will not affect the block and tx, if those
    /// have been filled.
    pub fn try_with_cfg<C, F, NewState, E>(
        mut self,
        cfg: &C,
        f: F,
    ) -> Result<Trevm<Db, Insp, NewState>, EvmErrored<Db, Insp, E>>
    where
        C: Cfg,
        F: FnOnce(Self) -> Result<Trevm<Db, Insp, NewState>, EvmErrored<Db, Insp, E>>,
        NewState: HasCfg,
    {
        let previous = self.inner.cfg().clone();
        cfg.fill_cfg(&mut self.inner);

        match f(self) {
            Ok(mut evm) => {
                evm.inner.modify_cfg(|cfg| *cfg = previous);
                Ok(evm)
            }
            Err(mut evm) => {
                evm.inner.modify_cfg(|cfg| *cfg = previous);
                Err(evm)
            }
        }
    }

    /// Set a limit beyond which a callframe's memory cannot be resized.
    /// Attempting to resize beyond this limit will result in a
    /// [OutOfGasError::Memory] error.
    ///
    /// In cases where the gas limit may be extraordinarily high, it is
    /// recommended to set this to a sane value to prevent memory allocation
    /// panics. Defaults to `2^32 - 1` bytes per EIP-1985.
    ///
    /// [OutOfGasError::Memory]: revm::context::result::OutOfGasError::Memory
    #[cfg(feature = "memory_limit")]
    pub fn set_memory_limit(&mut self, new_limit: u64) -> u64 {
        let mut ml = 0;
        self.inner.ctx.modify_cfg(|cfg| ml = core::mem::replace(&mut cfg.memory_limit, new_limit));
        ml
    }

    /// Disable balance checks. If the sender does not have enough balance to
    /// cover the transaction, the sender will be given enough ether to ensure
    /// execution doesn't fail.
    #[cfg(feature = "optional_balance_check")]
    pub fn disable_balance_check(&mut self) {
        self.inner.ctx.modify_cfg(|cfg| cfg.disable_balance_check = true)
    }

    /// Enable balance checks. See [`Self::disable_balance_check`].
    #[cfg(feature = "optional_balance_check")]
    pub fn enable_balance_check(&mut self) {
        self.inner.ctx.modify_cfg(|cfg| cfg.disable_balance_check = false)
    }

    /// Run a closure with balance checks disabled, then restore the previous
    /// setting.
    #[cfg(feature = "optional_balance_check")]
    pub fn without_balance_check<F, NewState: HasCfg>(mut self, f: F) -> Trevm<Db, Insp, NewState>
    where
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
    {
        let previous = self.inner.cfg().disable_balance_check;
        self.disable_balance_check();
        let mut new = f(self);
        new.inner.ctx.modify_cfg(|cfg| cfg.disable_balance_check = previous);
        new
    }

    /// Disable block gas limits. This allows transactions to execute even if
    /// they gas needs exceed the block gas limit. This is useful for
    /// simulating large transactions like forge scripts.
    #[cfg(feature = "optional_block_gas_limit")]
    pub fn disable_block_gas_limit(&mut self) {
        self.inner.ctx.modify_cfg(|cfg| cfg.disable_block_gas_limit = true);
    }

    /// Enable block gas limits. See [`Self::disable_block_gas_limit`].
    #[cfg(feature = "optional_block_gas_limit")]
    pub fn enable_block_gas_limit(&mut self) {
        self.inner.ctx.modify_cfg(|cfg| cfg.disable_block_gas_limit = false);
    }

    /// Run a closure with block gas limits disabled, then restore the previous
    /// setting.
    #[cfg(feature = "optional_block_gas_limit")]
    pub fn without_block_gas_limit<F, NewState: HasCfg>(mut self, f: F) -> Trevm<Db, Insp, NewState>
    where
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
    {
        let previous = self.inner.cfg().disable_block_gas_limit;
        self.disable_block_gas_limit();
        let mut new = f(self);
        new.inner.ctx.modify_cfg(|cfg| cfg.disable_block_gas_limit = previous);
        new
    }

    /// Disable [EIP-3607]. This allows transactions to originate from accounts
    /// that contain code. This is useful for simulating smart-contract calls.
    ///
    /// [EIP-3607]: https://eips.ethereum.org/EIPS/eip-3607
    #[cfg(feature = "optional_eip3607")]
    pub fn disable_eip3607(&mut self) {
        self.inner.ctx.modify_cfg(|cfg| cfg.disable_eip3607 = true);
    }

    /// Enable [EIP-3607]. See [`Self::disable_eip3607`].
    ///
    /// [EIP-3607]: https://eips.ethereum.org/EIPS/eip-3607
    #[cfg(feature = "optional_eip3607")]
    pub fn enable_eip3607(&mut self) {
        self.inner.ctx.modify_cfg(|cfg| cfg.disable_eip3607 = false);
    }

    /// Run a closure with [EIP-3607] disabled, then restore the previous
    /// setting.
    #[cfg(feature = "optional_eip3607")]
    pub fn without_eip3607<F, NewState: HasCfg>(mut self, f: F) -> Trevm<Db, Insp, NewState>
    where
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
    {
        let previous = self.inner.cfg().disable_eip3607;
        self.disable_eip3607();

        let mut new = f(self);
        new.inner.ctx.modify_cfg(|cfg| cfg.disable_eip3607 = previous);
        new
    }

    /// Disables [EIP-1559] base fee checks. This is useful for testing method
    /// calls with zero gas price.
    ///
    /// [EIP-1559]: https://eips.ethereum.org/EIPS/eip-1559
    #[cfg(feature = "optional_no_base_fee")]
    pub fn disable_base_fee(&mut self) {
        self.inner.ctx.modify_cfg(|cfg| cfg.disable_base_fee = true)
    }

    /// Enable [EIP-1559] base fee checks. See [`Self::disable_base_fee`].
    ///
    /// [EIP-1559]: https://eips.ethereum.org/EIPS/eip-1559
    #[cfg(feature = "optional_no_base_fee")]
    pub fn enable_base_fee(&mut self) {
        self.inner.ctx.modify_cfg(|cfg| cfg.disable_base_fee = false)
    }

    /// Run a closure with [EIP-1559] base fee checks disabled, then restore the
    /// previous setting.
    ///
    /// [EIP-1559]: https://eips.ethereum.org/EIPS/eip-1559
    #[cfg(feature = "optional_no_base_fee")]
    pub fn without_base_fee<F, NewState: HasCfg>(mut self, f: F) -> Trevm<Db, Insp, NewState>
    where
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
    {
        let previous = self.inner.cfg().disable_base_fee;
        self.disable_base_fee();

        let mut new = f(self);
        new.inner.ctx.modify_cfg(|cfg| cfg.disable_base_fee = previous);
        new
    }

    /// Disable nonce checks. This allows transactions to be sent with
    /// incorrect nonces, and is useful for things like system transactions.
    pub fn disable_nonce_check(&mut self) {
        self.inner.ctx.modify_cfg(|cfg| cfg.disable_nonce_check = true)
    }

    /// Enable nonce checks. See [`Self::disable_nonce_check`].
    pub fn enable_nonce_check(&mut self) {
        self.inner.ctx.modify_cfg(|cfg| cfg.disable_nonce_check = false)
    }

    /// Run a closure with nonce checks disabled, then restore the previous
    /// setting. This will not affect the block and tx, if those have been
    /// filled.
    pub fn without_nonce_check<F, NewState: HasCfg>(mut self, f: F) -> Trevm<Db, Insp, NewState>
    where
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
    {
        let previous = self.inner.cfg().disable_nonce_check;
        self.disable_nonce_check();

        let mut new = f(self);
        new.inner.ctx.modify_cfg(|cfg| cfg.disable_nonce_check = previous);
        new
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
