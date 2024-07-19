use crate::{
    syscall::{SystemCall, CONSOLIDATION_REQUEST_BYTES, WITHDRAWAL_REQUEST_BYTES},
    Block, BlockOutput, Cfg, EvmNeedsCfg, EvmNeedsFirstBlock, EvmNeedsNextBlock, EvmNeedsTx,
    EvmReady, HasCfg, HasOutputs, Lifecycle, NeedsBlock, PostTx, PostflightResult, Tx,
};
use alloy_consensus::{Receipt, Request};
use alloy_eips::{
    eip2935::{HISTORY_STORAGE_ADDRESS, HISTORY_STORAGE_CODE},
    eip7002::WithdrawalRequest,
    eip7251::ConsolidationRequest,
};
use alloy_primitives::{Address, Bytes, B256, U256};
use revm::{
    db::{states::bundle_state::BundleRetention, BundleState},
    primitives::{
        Account, AccountInfo, Bytecode, EVMError, EvmState, EvmStorageSlot, ExecutionResult,
        InvalidTransaction, ResultAndState, SpecId, BLOCKHASH_SERVE_WINDOW,
    },
    Database, DatabaseCommit, DatabaseRef, Evm, State,
};
use std::{
    collections::HashMap,
    convert::Infallible,
    fmt::{self, Debug},
    marker::PhantomData,
};

/// Trevm provides a type-safe interface to the EVM, using the typestate pattern.
///
/// See the [crate-level documentation](crate) for more information.
pub struct Trevm<'a, Ext, Db: Database, State> {
    inner: Box<Evm<'a, Ext, Db>>,
    outputs: Vec<BlockOutput>,
    _state: PhantomData<fn() -> State>,
}

impl<Ext, Db: Database, State> Debug for Trevm<'_, Ext, Db, State> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Trevm").finish_non_exhaustive()
    }
}

impl<'a, Ext, Db: Database, State> AsRef<Evm<'a, Ext, Db>> for Trevm<'a, Ext, Db, State> {
    fn as_ref(&self) -> &Evm<'a, Ext, Db> {
        &self.inner
    }
}

impl<'a, Ext, Db: Database> From<Evm<'a, Ext, Db>> for EvmNeedsCfg<'a, Ext, Db> {
    fn from(inner: Evm<'a, Ext, Db>) -> Self {
        Self { inner: Box::new(inner), outputs: Default::default(), _state: PhantomData }
    }
}

impl<'a, Ext, Db: Database, State> Trevm<'a, Ext, Db, State> {
    /// Get a reference to the current [`Evm`].
    pub fn inner(&self) -> &Evm<'a, Ext, Db> {
        self.as_ref()
    }

    /// Get a mutable reference to the current [`Evm`]. This should be used with
    /// caution, as modifying the EVM may lead to inconsistent state or invalid
    /// execution.
    pub fn inner_mut_unchecked(&mut self) -> &mut Evm<'a, Ext, Db> {
        &mut self.inner
    }

    /// Destructure the [`Trevm`] into its parts.
    pub fn into_parts(self) -> (Box<Evm<'a, Ext, Db>>, Vec<BlockOutput>) {
        (self.inner, self.outputs)
    }

    /// Get a reference to the outputs produced by block proessing so far.
    ///
    ///
    /// ## Note
    /// The outputs will:
    /// - be empty if the EVM has not received any block environment yet
    ///   (i.e. has never reached the [`EvmNeedsTx`] state).
    /// - contain a partially filled block output if the EVM is in the
    ///   [`EvmNeedsTx`] state.
    pub fn outputs(&self) -> &[BlockOutput] {
        &self.outputs
    }

    /// Get the id of the currently running hardfork spec. Convenience function
    /// calling [`Evm::spec_id`].
    pub fn spec_id(&self) -> SpecId {
        self.inner.spec_id()
    }

    /// Get the current account info for a specific address.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn try_read_account(&mut self, address: Address) -> Result<Option<AccountInfo>, Db::Error> {
        self.inner.db_mut().basic(address)
    }

    /// Get the current nonce for a specific address
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn try_read_nonce(&mut self, address: Address) -> Result<u64, Db::Error> {
        self.try_read_account(address).map(|a| a.map(|a| a.nonce).unwrap_or_default())
    }

    /// Get the current nonce for a specific address
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn try_read_balance(&mut self, address: Address) -> Result<U256, Db::Error> {
        self.try_read_account(address).map(|a| a.map(|a| a.balance).unwrap_or_default())
    }

    /// Get the value of a storage slot.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn try_read_storage(&mut self, address: Address, slot: U256) -> Result<U256, Db::Error> {
        self.inner.db_mut().storage(address, slot)
    }

    /// Get the code at the given account, if any.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn try_read_code(&mut self, address: Address) -> Result<Option<Bytecode>, Db::Error> {
        let acct_info = self.try_read_account(address)?;
        match acct_info {
            Some(acct) => Ok(Some(self.inner.db_mut().code_by_hash(acct.code_hash)?)),
            None => Ok(None),
        }
    }
}

impl<'a, Ext, Db: Database + DatabaseRef, State> Trevm<'a, Ext, Db, State> {
    /// Get the current account info for a specific address.
    pub fn try_read_account_ref(
        &self,
        address: Address,
    ) -> Result<Option<AccountInfo>, <Db as DatabaseRef>::Error> {
        self.inner.db().basic_ref(address)
    }

    /// Get the current nonce for a specific address
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn try_read_nonce_ref(&self, address: Address) -> Result<u64, <Db as DatabaseRef>::Error> {
        self.try_read_account_ref(address).map(|a| a.map(|a| a.nonce).unwrap_or_default())
    }

    /// Get the current nonce for a specific address
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn try_read_balance_ref(
        &self,
        address: Address,
    ) -> Result<U256, <Db as DatabaseRef>::Error> {
        self.try_read_account_ref(address).map(|a| a.map(|a| a.balance).unwrap_or_default())
    }

    /// Get the value of a storage slot.
    pub fn try_read_storage_ref(
        &self,
        address: Address,
        slot: U256,
    ) -> Result<U256, <Db as DatabaseRef>::Error> {
        self.inner.db().storage_ref(address, slot)
    }

    /// Get the code at the given account, if any.
    pub fn try_read_code_ref(
        &self,
        address: Address,
    ) -> Result<Option<Bytecode>, <Db as DatabaseRef>::Error> {
        let acct_info = self.try_read_account_ref(address)?;
        match acct_info {
            Some(acct) => Ok(Some(self.inner.db().code_by_hash_ref(acct.code_hash)?)),
            None => Ok(None),
        }
    }
}

impl<'a, Ext, Db: Database<Error = Infallible>, State> Trevm<'a, Ext, Db, State> {
    /// Get the current account info for a specific address.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn read_account(&mut self, address: Address) -> Option<AccountInfo> {
        self.inner.db_mut().basic(address).expect("infallible")
    }

    /// Get the current nonce for a specific address
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn read_nonce(&mut self, address: Address) -> u64 {
        self.read_account(address).map(|a: AccountInfo| a.nonce).unwrap_or_default()
    }

    /// Get the current nonce for a specific address
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn read_balance(&mut self, address: Address) -> U256 {
        self.read_account(address).map(|a: AccountInfo| a.balance).unwrap_or_default()
    }

    /// Get the value of a storage slot.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn read_storage(&mut self, address: Address, slot: U256) -> U256 {
        self.inner.db_mut().storage(address, slot).expect("infallible")
    }

    /// Get the code at the given account, if any.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn read_code(&mut self, address: Address) -> Option<Bytecode> {
        let acct_info = self.read_account(address)?;
        Some(self.inner.db_mut().code_by_hash(acct_info.code_hash).expect("infallible"))
    }
}

impl<'a, Ext, Db: Database<Error = Infallible> + DatabaseRef<Error = Infallible>, State>
    Trevm<'a, Ext, Db, State>
{
    /// Get the current account info for a specific address.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn read_account_ref(&self, address: Address) -> Option<AccountInfo> {
        self.inner.db().basic_ref(address).expect("infallible")
    }

    /// Get the current nonce for a specific address
    pub fn read_nonce_ref(&self, address: Address) -> u64 {
        self.read_account_ref(address).map(|a: AccountInfo| a.nonce).unwrap_or_default()
    }

    /// Get the current nonce for a specific address
    pub fn read_balance_ref(&self, address: Address) -> U256 {
        self.read_account_ref(address).map(|a: AccountInfo| a.balance).unwrap_or_default()
    }

    /// Get the value of a storage slot.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn read_storage_ref(&self, address: Address, slot: U256) -> U256 {
        self.inner.db().storage_ref(address, slot).expect("infallible")
    }

    /// Get the code at the given account, if any.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn read_code_ref(&self, address: Address) -> Option<Bytecode> {
        let acct_info = self.read_account_ref(address)?;
        Some(self.inner.db().code_by_hash_ref(acct_info.code_hash).expect("infallible"))
    }
}

impl<'a, Ext, Db: Database, EvmState> Trevm<'a, Ext, State<Db>, EvmState> {
    /// Set the [EIP-161] state clear flag, activated in the Spurious Dragon
    /// hardfork.
    pub fn set_state_clear_flag(&mut self, flag: bool) {
        self.inner.db_mut().set_state_clear_flag(flag)
    }
}

// --- NEEDS CFG

impl<'a, Ext, Db: Database> EvmNeedsCfg<'a, Ext, Db> {
    /// Fill the configuration environment.
    pub fn fill_cfg<T: Cfg>(mut self, filler: &T) -> EvmNeedsFirstBlock<'a, Ext, Db> {
        filler.fill_cfg(&mut self.inner);
        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { std::mem::transmute(self) }
    }
}

// --- HAS CFG

impl<'a, Ext, Db: Database, State: HasCfg> Trevm<'a, Ext, Db, State> {
    /// Set the [EIP-170] contract code size limit. By default this is set to
    /// 0x6000 bytes (~25KiB). Contracts whose bytecode is larger than this
    /// limit cannot be deployed and will produce a [`CreateInitCodeSizeLimit`]
    /// error.
    ///
    /// [`CreateInitCodeSizeLimit`]: InvalidTransaction::CreateInitCodeSizeLimit
    /// [`Eip-170`]: https://eips.ethereum.org/EIPS/eip-170
    pub fn set_code_size_limit(&mut self, limit: usize) -> Option<usize> {
        let cfg = self.inner.cfg_mut();
        cfg.limit_contract_code_size.replace(limit)
    }

    /// Disable the [EIP-170] contract code size limit, returning the previous
    /// setting.
    ///
    /// [`Eip-170`]: https://eips.ethereum.org/EIPS/eip-170
    pub fn disable_code_size_limit(&mut self) -> Option<usize> {
        self.inner.cfg_mut().limit_contract_code_size.take()
    }

    /// Run a closure with the code size limit disabled, then restore the
    /// previous setting.
    pub fn without_code_size_limit<F, NewState: HasCfg>(
        mut self,
        f: F,
    ) -> Trevm<'a, Ext, Db, NewState>
    where
        F: FnOnce(Self) -> Trevm<'a, Ext, Db, NewState>,
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
    /// [`CreateInitCodeSizeLimit`]: InvalidTransaction::CreateInitCodeSizeLimit
    /// [`Eip-170`]: https://eips.ethereum.org/EIPS/eip-170
    pub fn set_default_code_size_limit(&mut self) -> Option<usize> {
        self.set_code_size_limit(0x6000)
    }

    /// Set the KZG settings used for point evaluation precompiles. By default
    /// this is set to the settings used in the Ethereum mainnet.
    ///
    /// This is a low-level API, and is not intended for general use.
    #[cfg(feature = "kzg")]
    pub fn set_kzg_settings(
        &mut self,
        settings: revm::primitives::EnvKzgSettings,
    ) -> revm::primitives::EnvKzgSettings {
        let cfg = self.inner.cfg_mut();
        std::mem::replace(&mut cfg.kzg_settings, settings)
    }

    /// Set a limit beyond which a callframe's memory cannot be resized.
    /// Attempting to resize beyond this limit will result in a
    /// [OutOfGasError::Memory] error.
    ///
    /// In cases where the gas limit may be extraordinarily high, it is
    /// recommended to set this to a sane value to prevent memory allocation
    /// panics. Defaults to `2^32 - 1` bytes per EIP-1985.
    ///
    /// [OutOfGasError::Memory]: revm::primitives::OutOfGasError::Memory
    #[cfg(feature = "memory_limit")]
    pub fn set_memory_limit(&mut self, new_limit: u64) -> u64 {
        let cfg = self.inner.cfg_mut();
        std::mem::replace(&mut cfg.memory_limit, new_limit)
    }

    /// Disable balance checks. If the sender does not have enough balance to
    /// cover the transaction, the sender will be given enough ether to ensure
    /// execution doesn't fail.
    #[cfg(feature = "optional_balance_check")]
    pub fn disable_balance_check(&mut self) {
        self.inner.cfg_mut().disable_balance_check = true
    }

    /// Enable balance checks. See [`Self::disable_balance_check`].
    #[cfg(feature = "optional_balance_check")]
    pub fn enable_balance_check(&mut self) {
        self.inner.cfg_mut().disable_balance_check = false
    }

    /// Run a closure with balance checks disabled, then restore the previous
    /// setting.
    #[cfg(feature = "optional_balance_check")]
    pub fn without_balance_check<F, NewState: HasCfg>(
        mut self,
        f: F,
    ) -> Trevm<'a, Ext, Db, NewState>
    where
        F: FnOnce(Self) -> Trevm<'a, Ext, Db, NewState>,
    {
        let previous = self.inner.cfg().disable_balance_check;
        self.disable_balance_check();
        let mut new = f(self);
        new.inner.cfg_mut().disable_balance_check = previous;
        new
    }

    /// Disable block gas limits. This allows transactions to execute even if
    /// they gas needs exceed the block gas limit. This is useful for
    /// simulating large transactions like forge scripts.
    #[cfg(feature = "optional_block_gas_limit")]
    pub fn disable_block_gas_limit(&mut self) {
        self.inner.cfg_mut().disable_beneficiary_reward = true
    }

    /// Enable block gas limits. See [`Self::disable_block_gas_limit`].
    #[cfg(feature = "optional_block_gas_limit")]
    pub fn enable_block_gas_limit(&mut self) {
        self.inner.cfg_mut().disable_beneficiary_reward = false
    }

    /// Run a closure with block gas limits disabled, then restore the previous
    /// setting.
    #[cfg(feature = "optional_block_gas_limit")]
    pub fn without_block_gas_limit<F, NewState: HasCfg>(
        mut self,
        f: F,
    ) -> Trevm<'a, Ext, Db, NewState>
    where
        F: FnOnce(Self) -> Trevm<'a, Ext, Db, NewState>,
    {
        let previous = self.inner.cfg().disable_block_gas_limit;
        self.disable_block_gas_limit();
        let mut new = f(self);
        new.inner.cfg_mut().disable_block_gas_limit = previous;
        new
    }

    /// Disable [EIP-3607]. This allows transactions to originate from accounts
    /// that contain code. This is useful for simulating smart-contract calls.
    ///
    /// [EIP-3607]: https://eips.ethereum.org/EIPS/eip-3607
    #[cfg(feature = "optional_eip3607")]
    pub fn disable_eip3607(&mut self) {
        self.inner.cfg_mut().disable_eip3607 = true
    }

    /// Enable [EIP-3607]. See [`Self::disable_eip3607`].
    ///
    /// [EIP-3607]: https://eips.ethereum.org/EIPS/eip-3607
    #[cfg(feature = "optional_eip3607")]
    pub fn enable_eip3607(&mut self) {
        self.inner.cfg_mut().disable_eip3607 = false
    }

    /// Run a closure with [EIP-3607] disabled, then restore the previous
    /// setting.
    #[cfg(feature = "optional_eip3607")]
    pub fn without_eip3607<F, NewState: HasCfg>(mut self, f: F) -> Trevm<'a, Ext, Db, NewState>
    where
        F: FnOnce(Self) -> Trevm<'a, Ext, Db, NewState>,
    {
        let previous = self.inner.cfg().disable_eip3607;
        self.disable_eip3607();
        let mut new = f(self);
        new.inner.cfg_mut().disable_eip3607 = previous;
        new
    }

    /// Disables all gas refunds. This is useful when using chains that have
    /// gas refunds disabled e.g. Avalanche. Reasoning behind removing gas
    /// refunds can be found in [EIP-3298].
    /// By default, it is set to `false`.
    ///
    /// [EIP-3298]: https://eips.ethereum.org/EIPS/eip-3298
    #[cfg(feature = "optional_gas_refund")]
    pub fn disable_gas_refund(&mut self) {
        self.inner.cfg_mut().disable_gas_refund = true
    }

    /// Enable gas refunds. See [`Self::disable_gas_refund`].
    #[cfg(feature = "optional_gas_refund")]
    pub fn enable_gas_refund(&mut self) {
        self.inner.cfg_mut().disable_gas_refund = false
    }

    /// Run a closure with gas refunds disabled, then restore the previous
    /// setting.
    #[cfg(feature = "optional_gas_refund")]
    pub fn without_gas_refund<F, NewState: HasCfg>(mut self, f: F) -> Trevm<'a, Ext, Db, NewState>
    where
        F: FnOnce(Self) -> Trevm<'a, Ext, Db, NewState>,
    {
        let previous = self.inner.cfg().disable_gas_refund;
        self.disable_gas_refund();
        let mut new = f(self);
        new.inner.cfg_mut().disable_gas_refund = previous;
        new
    }

    /// Disables [EIP-1559] base fee checks. This is useful for testing method
    /// calls with zero gas price.
    ///
    /// [EIP-1559]: https://eips.ethereum.org/EIPS/eip-1559
    #[cfg(feature = "optional_no_base_fee")]
    pub fn disable_base_fee(&mut self) {
        self.inner.cfg_mut().disable_base_fee = true;
    }

    /// Enable [EIP-1559] base fee checks. See [`Self::disable_base_fee`].
    ///
    /// [EIP-1559]: https://eips.ethereum.org/EIPS/eip-1559
    #[cfg(feature = "optional_no_base_fee")]
    pub fn enable_base_fee(&mut self) {
        self.inner.cfg_mut().disable_base_fee = false
    }

    /// Run a closure with [EIP-1559] base fee checks disabled, then restore the
    /// previous setting.
    ///
    /// [EIP-1559]: https://eips.ethereum.org/EIPS/eip-1559
    #[cfg(feature = "optional_no_base_fee")]
    pub fn without_base_fee<F, NewState: HasCfg>(mut self, f: F) -> Trevm<'a, Ext, Db, NewState>
    where
        F: FnOnce(Self) -> Trevm<'a, Ext, Db, NewState>,
    {
        let previous = self.inner.cfg().disable_base_fee;
        self.disable_base_fee();
        let mut new = f(self);
        new.inner.cfg_mut().disable_base_fee = previous;
        new
    }

    /// Disable the payout of the block and gas fees to the block beneficiary.
    #[cfg(feature = "optional_beneficiary_reward")]
    pub fn disable_beneficiary_reward(&mut self) {
        self.inner.cfg_mut().disable_beneficiary_reward = true;
    }

    /// Enable the payout of the block and gas fees to the block beneficiary.
    /// See [`Self::disable_beneficiary_reward`].
    #[cfg(feature = "optional_beneficiary_reward")]
    pub fn enable_beneficiary_reward(&mut self) {
        self.inner.cfg_mut().disable_beneficiary_reward = false
    }

    /// Run a closure with the block and gas fees payout disabled, then restore
    /// the previous setting.
    #[cfg(feature = "optional_beneficiary_reward")]
    pub fn without_beneficiary_reward<F, NewState: HasCfg>(
        mut self,
        f: F,
    ) -> Trevm<'a, Ext, Db, NewState>
    where
        F: FnOnce(Self) -> Trevm<'a, Ext, Db, NewState>,
    {
        let previous = self.inner.cfg().disable_beneficiary_reward;
        self.disable_beneficiary_reward();
        let mut new = f(self);
        new.inner.cfg_mut().disable_beneficiary_reward = previous;
        new
    }
}

// --- NEEDS BLOCK

impl<'a, Ext, Db: Database, State: NeedsBlock> Trevm<'a, Ext, Db, State> {
    /// Create new block outputs, to be filled by executing transactions.
    fn new_block_outputs(&mut self, tx_hint: usize) {
        self.outputs.push(BlockOutput::with_capacity(tx_hint));
    }

    /// Fill the block environment. This is a low-level API, and is not intended
    /// for general use, as it will not perform pre-block logic such as applying
    /// pre-block hooks introduced in [EIP-4788] or [EIP-2935].
    ///
    /// Prefer using [`Self::open_block`] instead.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    /// [EIP-2935]: https://eips.ethereum.org/EIPS/eip-2935
    pub fn fill_block<B: Block>(mut self, filler: &B) -> EvmNeedsTx<'a, Ext, Db> {
        filler.fill_block(&mut self.inner);
        self.new_block_outputs(filler.tx_count_hint().unwrap_or(10));
        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { std::mem::transmute(self) }
    }
}

impl<'a, Ext, Db: Database + DatabaseCommit, EvmState: NeedsBlock>
    Trevm<'a, Ext, State<Db>, EvmState>
{
    /// Open a block, apply some logic, and return the EVM ready for the next
    /// transaction.
    ///
    /// This is intended to be used for pre-block logic, such as applying
    /// pre-block hooks introduced in [EIP-4788] or [EIP-2935].
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    /// [EIP-2935]: https://eips.ethereum.org/EIPS/eip-2935
    pub fn open_block<B, L>(
        self,
        filler: &B,
        lifecycle: &mut L,
    ) -> Result<EvmNeedsTx<'a, Ext, State<Db>>, TransactedError<'a, Ext, State<Db>>>
    where
        B: Block,
        L: Lifecycle<'a, Ext, Db>,
    {
        lifecycle.open_block(self, filler)
    }
}

// --- HAS OUTPUTS

impl<'a, Ext, Db: Database, State: HasOutputs> Trevm<'a, Ext, Db, State> {
    /// Get the current block's outputs.
    pub fn current_output(&self) -> &BlockOutput {
        self.outputs.last().expect("never empty")
    }

    /// Get the current block's outputs. Modification is discouraged as it may
    /// lead to inconsistent state or invalid execution.
    pub fn current_output_mut_unchecked(&mut self) -> &mut BlockOutput {
        self.outputs.last_mut().expect("never empty")
    }
}

impl<'a, Ext, Db: Database, Missing: HasOutputs> Trevm<'a, Ext, State<Db>, Missing> {
    /// Finish execution and return the outputs.
    ///
    /// ## Panics
    ///
    /// If the State has not been built with StateBuilder::with_bundle_update.
    ///
    /// See [`State::merge_transitions`] and `State::take_bundle`.
    pub fn finish(self) -> (BundleState, Vec<BlockOutput>)
    where
        Db: DatabaseCommit,
    {
        let Self { outputs, inner: mut evm, .. } = self;

        evm.db_mut().merge_transitions(BundleRetention::Reverts);
        let bundle = evm.db_mut().take_bundle();

        (bundle, outputs)
    }
}

// --- NEEDS FIRST TX

impl<'a, Ext, Db: Database> EvmNeedsTx<'a, Ext, Db> {
    fn commit_state(&mut self, state: EvmState)
    where
        Db: DatabaseCommit,
    {
        self.inner.db_mut().commit(state);
    }

    /// Accumulate the result of a transaction.
    fn push_to_outputs(&mut self, result: ExecutionResult)
    where
        Db: DatabaseCommit,
    {
        let sender = self.inner.tx().caller;
        let cumulative_gas_used =
            self.current_output().cumulative_gas_used().saturating_add(result.gas_used() as u128);

        // Must be created after use_block_gas
        let receipt = Receipt {
            status: result.is_success().into(),
            cumulative_gas_used,
            logs: result.into_logs(),
        };

        let parse_deposits = self.spec_id() >= SpecId::PRAGUE;
        self.current_output_mut_unchecked().push_result(receipt, sender, parse_deposits);
    }

    /// Clear the current block environment.
    ///
    /// This is a low-level API, and is not intended for general use, as it
    /// will not perform post-block logic such as applying post-block hooks
    /// introduced in [EIP-7002] or [EIP-7251].
    ///
    /// Prefer using [`Self::close_block`] instead.
    ///
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    /// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
    pub fn clear_block(mut self) -> EvmNeedsNextBlock<'a, Ext, Db> {
        self.inner.as_mut().block_mut().clear();
        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { std::mem::transmute(self) }
    }

    /// Fill the transaction environment.
    pub fn fill_tx<T: Tx>(mut self, filler: &T) -> EvmReady<'a, Ext, Db> {
        filler.fill_tx(&mut self.inner);
        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { std::mem::transmute(self) }
    }

    /// Execute a transaction. Shortcut for `fill_tx(tx).execute_tx()`.
    pub fn execute_tx<T: Tx>(
        self,
        filler: &T,
    ) -> Result<Transacted<'a, Ext, Db>, TransactedError<'a, Ext, Db>> {
        self.fill_tx(filler).execute_tx()
    }

    /// Apply the pre-block logic for [EIP-2935]. This logic was introduced in
    /// Prague and updates historical block hashes in a special system
    /// contract. Unlike other system transactions, this is NOT modeled as a transaction.
    ///
    /// [EIP-2935]: https://eips.ethereum.org/EIPS/eip-2935
    pub fn apply_eip2935(mut self) -> Result<Self, TransactedError<'a, Ext, Db>>
    where
        Db: DatabaseCommit,
    {
        if self.spec_id() < SpecId::PRAGUE || self.inner.block().number.is_zero() {
            return Ok(self);
        }

        let mut account: Account = match self.inner.db_mut().basic(HISTORY_STORAGE_ADDRESS) {
            Ok(Some(account)) => account,
            Ok(None) => AccountInfo {
                nonce: 1,
                code: Some(Bytecode::new_raw(HISTORY_STORAGE_CODE.clone())),
                ..Default::default()
            },
            Err(error) => {
                return Err(TransactedError { evm: self, error: EVMError::Database(error) })
            }
        }
        .into();

        let block_num = self.inner.block().number.as_limbs()[0];
        let prev_block = block_num.saturating_sub(1);

        // Update the EVM state with the new value.
        {
            let slot = U256::from(block_num % BLOCKHASH_SERVE_WINDOW as u64);
            let current_hash = match self.inner.db_mut().storage(HISTORY_STORAGE_ADDRESS, slot) {
                Ok(current_hash) => current_hash,
                Err(error) => {
                    return Err(TransactedError { evm: self, error: EVMError::Database(error) })
                }
            };
            let parent_block_hash = match self.inner.db_mut().block_hash(prev_block) {
                Ok(parent_block_hash) => parent_block_hash,
                Err(error) => {
                    return Err(TransactedError { evm: self, error: EVMError::Database(error) })
                }
            };

            // Insert the state change for the slot
            let value = EvmStorageSlot::new_changed(current_hash, parent_block_hash.into());

            account.storage.insert(slot, value);
        }

        // Mark the account as touched and commit the state change
        account.mark_touch();
        self.inner.db_mut().commit(HashMap::from([(HISTORY_STORAGE_ADDRESS, account)]));

        Ok(self)
    }

    /// Apply a system transaction as specified in [EIP-4788], [EIP-7002], or
    /// [EIP-7251]. This function will execute the system transaction and apply
    /// the result if non-error, cleaning up any extraneous state changes, and
    /// restoring the block environment.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    /// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
    pub fn execute_system_tx(
        mut self,
        syscall: &SystemCall,
    ) -> Result<Transacted<'a, Ext, Db>, TransactedError<'a, Ext, Db>>
    where
        Db: DatabaseCommit,
    {
        let limit = U256::from(self.inner.tx().gas_limit);
        let old_gas_limit = std::mem::replace(&mut self.inner.block_mut().gas_limit, limit);
        let old_base_fee = std::mem::replace(&mut self.inner.block_mut().basefee, U256::ZERO);

        let trevm = self.fill_tx(syscall);
        let result = trevm.execute_tx();

        // Cleanup the syscall. For an error we need to reset the block env.
        // For a success, we need to also remove fees, the system caller nonce,
        // and the system caller account.
        let trevm = result
            .map(|t| t.cleanup_syscall(syscall, old_gas_limit, old_base_fee))
            .map_err(|e| e.cleanup_syscall(old_gas_limit, old_base_fee))?;

        // apply result, remove receipt from block outputs.
        Ok(trevm)
    }

    /// Apply a system transaction as specified in [EIP-4788]. The EIP-4788
    /// pre-block action was introduced in Cancun, and calls the beacon root
    /// contract to update the historical beacon root.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn apply_eip4788(
        self,
        parent_beacon_root: B256,
    ) -> Result<Self, TransactedError<'a, Ext, Db>>
    where
        Db: DatabaseCommit,
    {
        if self.spec_id() < SpecId::CANCUN {
            return Ok(self);
        }
        self.execute_system_tx(&SystemCall::eip4788(parent_beacon_root)).map(Transacted::apply_sys)
    }

    /// Apply a system transaction as specified in [EIP-7002]. The EIP-7002
    /// post-block action was introduced in Prague, and calls the withdrawal
    /// request contract to process withdrawal requests.
    ///
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    pub fn apply_eip7002(self) -> Result<Self, TransactedError<'a, Ext, Db>>
    where
        Db: DatabaseCommit,
    {
        if self.spec_id() < SpecId::PRAGUE {
            return Ok(self);
        }
        let mut res = self.execute_system_tx(&SystemCall::eip7002())?;

        // We make assumptions here:
        // - The system transaction never reverts.
        // - The system transaction always has an output.
        // - The system contract produces correct output.
        // - The output is a list of withdrawal requests.
        // - The output does not contain incomplete requests.

        let Some(output) = res.output() else { panic!("no output") };
        let reqs = output
            .chunks_exact(WITHDRAWAL_REQUEST_BYTES)
            .map(|chunk| {
                let mut req: WithdrawalRequest = Default::default();

                req.source_address.copy_from_slice(&chunk[0..20]);
                req.validator_pubkey.copy_from_slice(&chunk[20..68]);
                req.amount = u64::from_be_bytes(chunk[68..76].try_into().unwrap());

                Request::WithdrawalRequest(req)
            })
            .collect();
        res.evm.current_output_mut_unchecked().extend_requests(reqs);

        Ok(res.apply_sys())
    }

    /// Apply a system transaction as specified in [EIP-7251]. The EIP-7251
    /// post-block action calls the consolidation request contract to process
    pub fn apply_eip7251(self) -> Result<Self, TransactedError<'a, Ext, Db>>
    where
        Db: DatabaseCommit,
    {
        if self.spec_id() < SpecId::PRAGUE {
            return Ok(self);
        }

        let mut res = self.execute_system_tx(&SystemCall::eip7251())?;

        // We make assumptions here:
        // - The system transaction never reverts.
        // - The system transaction always has an output.
        // - The system contract produces correct output.
        // - The output is a list of consolidation requests.
        // - The output does not contain incomplete requests.

        let Some(output) = res.output() else { panic!("no output") };
        let reqs = output
            .chunks_exact(CONSOLIDATION_REQUEST_BYTES)
            .map(|chunk| {
                let mut req: ConsolidationRequest = Default::default();

                req.source_address.copy_from_slice(&chunk[0..20]);
                req.source_pubkey.copy_from_slice(&chunk[20..68]);
                req.target_pubkey.copy_from_slice(&chunk[68..116]);

                Request::ConsolidationRequest(req)
            })
            .collect();
        res.evm.current_output_mut_unchecked().extend_requests(reqs);

        Ok(res.apply_sys())
    }

    /// Run a transaction and apply the result if non-error. Shortcut for
    /// `execute_tx(tx).map(Transacted::apply)`.
    pub fn apply_tx<T: Tx>(self, filler: &T) -> Result<Self, TransactedError<'a, Ext, Db>>
    where
        Db: DatabaseCommit,
    {
        self.execute_tx(filler).map(Transacted::apply)
    }

    /// Run a transaction, apply the result if non-error and the predicate
    /// passes. Shortcut for `execute_tx(tx).map(|t| t.apply_if(f))`.
    pub fn apply_with_postcondition<T, F>(
        self,
        filler: &T,
        f: &mut F,
    ) -> Result<(PostflightResult, Self), TransactedError<'a, Ext, Db>>
    where
        Db: DatabaseCommit,
        T: Tx,
        F: PostTx,
    {
        self.execute_tx(filler).map(|t| t.apply_with_postcondition(f))
    }

    /// Execute the transactions from a block, without system actions.
    ///
    /// # Notes
    ///
    /// This function is intended to be used when validating a block that is
    /// expected to be good. It will execute all transactions in the block, and
    /// apply the results. This operation is not currently recoverable. If it
    /// fails, the EVM will be left in an inconsistent state.
    ///
    /// This function will NOT apply any system actions such as pre/post block
    /// hooks introduced in EIPs like [EIP-2935], [EIP-4788], [EIP-7002],
    /// [EIP-7251].
    ///
    /// [EIP-2935]: https://eips.ethereum.org/EIPS/eip-2935
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    /// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
    //
    // TODO: make it recoverable
    pub fn apply_txns<'b, I, T>(
        self,
        txns: I,
    ) -> Result<EvmNeedsTx<'a, Ext, Db>, EVMError<Db::Error>>
    where
        I: IntoIterator<Item = &'b T>,
        T: Tx + 'b,
        Db: DatabaseCommit,
    {
        let f = |_: &ResultAndState| true;
        self.execute_block_txns_apply_with_postconditions(txns, f)
    }

    /// Execute the transactions from a block, applying a check to each
    /// transaction output.
    ///
    /// This function is used for rollups and other cases where the block may
    /// contain invalid transactions. The check is applied to each transaction
    /// and if it returns true, the transaction is applied. If it returns
    /// false, the transaction is discarded.
    ///
    /// # Notes
    ///
    /// This function is intended to be used when validating a block that is
    /// expected to be good. It will execute all transactions in the block, and
    /// apply the results. This operation is not currently recoverable. If it
    /// fails, the EVM will be left in an inconsistent state.
    ///
    /// This function will NOT apply any system actions such as pre/post block
    /// hooks introduced in EIPs like [EIP-2935], [EIP-4788], [EIP-7002],
    /// [EIP-7251].
    ///
    /// [EIP-2935]: https://eips.ethereum.org/EIPS/eip-2935
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    /// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
    //
    // TODO: make it recoverable
    pub fn execute_block_txns_apply_with_postconditions<'b, I, T, F>(
        self,
        txns: I,
        mut f: F,
    ) -> Result<EvmNeedsTx<'a, Ext, Db>, EVMError<Db::Error>>
    where
        I: IntoIterator<Item = &'b T>,
        T: Tx + 'b,
        Db: DatabaseCommit,
        F: PostTx,
    {
        let mut evm = self;
        for tx in txns {
            evm = evm.apply_with_postcondition(tx, &mut f).map_err(TransactedError::into_error)?.1;
        }

        Ok(evm)
    }
}

impl<'a, Ext, Db: Database + DatabaseCommit> EvmNeedsTx<'a, Ext, State<Db>> {
    /// Close the current block, applying some logic, and returning the EVM
    /// ready for the next block.
    ///
    /// This is intended to be used for post-block logic, such as applying
    /// post-block hooks introduced in [EIP-7002] or [EIP-7251].
    ///
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    /// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
    pub fn close_block<L>(
        self,
        lifecycle: &mut L,
    ) -> Result<EvmNeedsNextBlock<'a, Ext, State<Db>>, TransactedError<'a, Ext, State<Db>>>
    where
        L: Lifecycle<'a, Ext, Db>,
    {
        lifecycle.close_block(self).map(EvmNeedsTx::clear_block)
    }
}

// --- READY

impl<'a, Ext, Db: Database> EvmReady<'a, Ext, Db> {
    /// Clear the current transaction environment.
    pub fn clear_tx(self) -> EvmNeedsTx<'a, Ext, Db> {
        // NB: we do not clear the tx env here, as we read it during `accumulate_result`. This behavior is documented for users in the `Filler` trait.

        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { std::mem::transmute(self) }
    }

    /// Execute the loaded transaction.
    pub fn execute_tx(mut self) -> Result<Transacted<'a, Ext, Db>, TransactedError<'a, Ext, Db>> {
        let result = self.inner.transact();
        let evm = self.clear_tx();

        match result {
            Ok(result) => Ok(Transacted { evm, result }),
            Err(error) => Err(TransactedError { evm, error }),
        }
    }
}

/// The error outcome of [`EvmReady::execute_tx`].
pub struct TransactedError<'a, Ext, Db: Database, E = EVMError<<Db as Database>::Error>> {
    evm: EvmNeedsTx<'a, Ext, Db>,
    error: E,
}

impl<Ext, Db: Database, E> fmt::Debug for TransactedError<'_, Ext, Db, E>
where
    E: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TransactedError").field("error", &self.error).finish_non_exhaustive()
    }
}

impl<'a, Ext, Db: Database, E> AsRef<EvmNeedsTx<'a, Ext, Db>> for TransactedError<'a, Ext, Db, E> {
    fn as_ref(&self) -> &EvmNeedsTx<'a, Ext, Db> {
        &self.evm
    }
}

impl<'a, Ext, Db: Database, E> TransactedError<'a, Ext, Db, E> {
    /// Create a new `TransactedError`.
    pub fn new(evm: EvmNeedsTx<'a, Ext, Db>, error: E) -> Self {
        Self { evm, error }
    }

    /// Clean up the system call, restoring the block env.
    fn cleanup_syscall(mut self, old_gas_limit: U256, old_base_fee: U256) -> Self {
        self.evm.inner.block_mut().gas_limit = old_gas_limit;
        self.evm.inner.block_mut().basefee = old_base_fee;
        self
    }

    /// Get a reference to the error.
    pub fn error(&self) -> &E {
        &self.error
    }

    /// Get a reference to the EVM.
    pub fn evm(&self) -> &EvmNeedsTx<'a, Ext, Db> {
        self.as_ref()
    }

    /// Destructure the `TransactedError` into its parts.
    pub fn into_parts(self) -> (EvmNeedsTx<'a, Ext, Db>, E) {
        (self.evm, self.error)
    }

    /// Inspect the error with a closure.
    pub fn inspect_error<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&E) -> T,
    {
        f(&self.error)
    }

    /// Discard the error and return the EVM.
    pub fn discard_error(self) -> EvmNeedsTx<'a, Ext, Db> {
        self.evm
    }

    /// Convert the error into an [`EVMError`].
    pub fn into_error(self) -> E {
        self.error
    }
}

impl<'a, Ext, Db: Database> TransactedError<'a, Ext, Db> {
    /// Check if the error is a transaction error. This is provided as a
    /// convenience function for common cases, as Transaction errors should
    /// usually be discarded.
    pub fn is_transaction_error(&self) -> bool {
        matches!(self.error, EVMError::Transaction(_))
    }

    /// Fallible cast to a [`InvalidTransaction`].
    pub fn as_transaction_err(&self) -> Option<&InvalidTransaction> {
        match &self.error {
            EVMError::Transaction(err) => Some(err),
            _ => None,
        }
    }

    /// Discard the error if it is a transaction error, returning the EVM. If
    /// the error is not a transaction error, return self
    pub fn discard_transaction_error(self) -> Result<EvmNeedsTx<'a, Ext, Db>, Self> {
        if self.is_transaction_error() {
            Ok(self.discard_error())
        } else {
            Err(self)
        }
    }
}

/// The success outcome of a [`EvmReady::execute_tx`] call.
///
/// This struct contains the EVM and the result of the transaction. You should
/// either [`apply`] the result or [`discard`] it. You can inspect the
/// [`ResultAndState`] using the [`result_and_state`] method.
///
/// The [`apply_if`] and [`apply_with_postcondition`] methods allow you to
/// apply the result conditionally, by making checks on the outcome.
///
/// [`apply`]: Self::apply
/// [`discard`]: Self::discard
/// [`result_and_state`]: Self::result
/// [`apply_if`]: Self::apply_if
/// [`apply_with_postcondition`]: Self::apply_with_postcondition
pub struct Transacted<'a, Ext, Db: Database> {
    /// The evm, with the transaction cleared.
    evm: EvmNeedsTx<'a, Ext, Db>,
    result: ResultAndState,
}

impl<Ext, Db: Database> fmt::Debug for Transacted<'_, Ext, Db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Transacted").finish_non_exhaustive()
    }
}

impl<'a, Ext, Db: Database> AsRef<EvmNeedsTx<'a, Ext, Db>> for Transacted<'a, Ext, Db> {
    fn as_ref(&self) -> &EvmNeedsTx<'a, Ext, Db> {
        &self.evm
    }
}

impl<'a, Ext, Db: Database> AsRef<ResultAndState> for Transacted<'a, Ext, Db> {
    fn as_ref(&self) -> &ResultAndState {
        &self.result
    }
}

impl<'a, Ext, Db: Database> AsRef<ExecutionResult> for Transacted<'a, Ext, Db> {
    fn as_ref(&self) -> &ExecutionResult {
        &self.result.result
    }
}

impl<'a, Ext, Db: Database> Transacted<'a, Ext, Db> {
    /// Clean up the system call, removing the system caller and fees, and
    /// restoring the block environment.
    fn cleanup_syscall(
        mut self,
        syscall: &SystemCall,
        old_gas_limit: U256,
        old_base_fee: U256,
    ) -> Self {
        // Restore the gas limit and base fee
        self.evm.inner.block_mut().gas_limit = old_gas_limit;
        self.evm.inner.block_mut().basefee = old_base_fee;

        // Remove the system caller and fees from the state
        let coinbase = self.evm.inner.block().coinbase;
        let state = self.state_mut_unchecked();
        state.remove(&syscall.caller);
        state.remove(&coinbase);

        self
    }

    /// Get a reference to the result.
    pub fn result(&self) -> &ExecutionResult {
        self.as_ref()
    }

    /// Get a mutable reference to the result. Modification of the result is
    /// discouraged, as it may lead to inconsistent state.
    ///
    /// This is primarily intended for use in [`SystemCall`] execution.
    ///
    /// [`SystemCall`]: crate::syscall::SystemCall
    pub fn result_mut_unchecked(&mut self) -> &mut ExecutionResult {
        &mut self.result.result
    }

    /// Get a reference to the state.
    pub fn state(&self) -> &EvmState {
        &self.result.state
    }

    /// Get a mutable reference to the state. Modification of the state is
    /// discouraged, as it may lead to inconsistent state.
    pub fn state_mut_unchecked(&mut self) -> &mut EvmState {
        &mut self.result.state
    }

    /// Get a reference to the result and state.
    pub fn result_and_state(&self) -> &ResultAndState {
        self.as_ref()
    }

    /// Get a mutable reference to the result and state. Modification of the
    /// result and state is discouraged, as it may lead to inconsistent state.
    ///
    /// This is primarily intended for use in [`SystemCall`] execution.
    ///
    /// [`SystemCall`]: crate::syscall::SystemCall
    pub fn result_and_state_mut_unchecked(&mut self) -> &mut ResultAndState {
        &mut self.result
    }

    /// Get the output of the transaction. This is the return value of the
    /// outermost callframe.
    pub fn output(&self) -> Option<&Bytes> {
        self.result().output()
    }

    /// Get the output of the transaction, and decode it as the return value of
    /// a [`SolCall`]. If `validate` is true, the output will be type- and
    /// range-checked.
    ///
    /// [`SolCall`]: alloy_sol_types::SolCall
    pub fn output_sol<T: alloy_sol_types::SolCall>(
        &self,
        validate: bool,
    ) -> Option<alloy_sol_types::Result<T::Return>>
    where
        T::Return: alloy_sol_types::SolType,
    {
        self.output().map(|output| T::abi_decode_returns(output, validate))
    }

    /// Get the gas used by the transaction.
    pub fn gas_used(&self) -> u64 {
        self.result.result.gas_used()
    }

    /// Get a reference to the EVM.
    pub fn evm(&self) -> &EvmNeedsTx<'a, Ext, Db> {
        self.as_ref()
    }

    /// Destructure the `Transacted` into its parts.
    pub fn into_parts(self) -> (EvmNeedsTx<'a, Ext, Db>, ResultAndState) {
        (self.evm, self.result)
    }

    /// Discard the state changes and return the EVM.
    pub fn discard(self) -> EvmNeedsTx<'a, Ext, Db> {
        self.evm
    }
}

impl<'a, Ext, Db: Database + DatabaseCommit> Transacted<'a, Ext, Db> {
    /// Apply the state changes, update the [`BlockOutput`], and return the EVM.
    pub fn apply(self) -> EvmNeedsTx<'a, Ext, Db> {
        let (mut evm, result) = self.into_parts();

        evm.commit_state(result.state);
        evm.push_to_outputs(result.result);

        evm
    }

    /// Apply the state changes, do not update the [`BlockOutput`], and return
    /// the EVM. This is useful for system transactions like those specified in
    /// [EIP-4788], [EIP-7002], or [EIP-7251], and should not generally be used
    /// outside of those contexts.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    /// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
    pub fn apply_sys(self) -> EvmNeedsTx<'a, Ext, Db> {
        let (mut evm, result) = self.into_parts();

        evm.commit_state(result.state);

        evm
    }

    /// Apply a predicate to the result and accept or reject based on the
    /// result. Returns a tuple of the choice and the EVM.
    pub fn apply_if<F, T>(self, f: F) -> (PostflightResult, EvmNeedsTx<'a, Ext, Db>)
    where
        F: FnOnce(&ResultAndState) -> T,
        T: Into<PostflightResult>,
    {
        let choice = f(&self.result).into();

        let evm = if choice.is_apply() { self.apply() } else { self.discard() };
        (choice, evm)
    }

    /// Apply a [`PostTx`] to the result and accept or reject based on
    /// the result. Returns a tuple of the choice and the EVM.
    pub fn apply_with_postcondition<F>(
        self,
        f: &mut F,
    ) -> (PostflightResult, EvmNeedsTx<'a, Ext, Db>)
    where
        F: PostTx,
    {
        let choice = f.run_post_tx(&self.result);

        let evm = if choice.is_apply() { self.apply() } else { self.discard() };
        (choice, evm)
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
