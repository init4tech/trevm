use crate::{
    driver::DriveBlockResult, est::EstimationResult, fillers::GasEstimationFiller,
    unwrap_or_trevm_err, Block, BlockDriver, BundleDriver, Cfg, ChainDriver, DriveBundleResult,
    DriveChainResult, ErroredState, EvmErrored, EvmExtUnchecked, EvmNeedsBlock, EvmNeedsCfg,
    EvmNeedsTx, EvmReady, EvmTransacted, HasBlock, HasCfg, HasTx, NeedsCfg, NeedsTx, Ready,
    TransactedState, Tx, MIN_TRANSACTION_GAS,
};
use alloy::{
    primitives::{Address, Bytes, U256},
    rpc::types::{state::StateOverride, BlockOverrides},
};
use core::convert::Infallible;
use revm::{
    db::{states::bundle_state::BundleRetention, BundleState, State},
    interpreter::gas::CALL_STIPEND,
    primitives::{
        AccountInfo, BlockEnv, Bytecode, EVMError, EvmState, ExecutionResult, InvalidTransaction,
        ResultAndState, SpecId, TxEnv, TxKind, KECCAK_EMPTY,
    },
    Database, DatabaseCommit, DatabaseRef, Evm,
};
use std::fmt;

/// Trevm provides a type-safe interface to the EVM, using the typestate pattern.
///
/// See the [crate-level documentation](crate) for more information.
pub struct Trevm<'a, Ext, Db: Database + DatabaseCommit, TrevmState> {
    pub(crate) inner: Box<Evm<'a, Ext, Db>>,
    pub(crate) state: TrevmState,
}

impl<Ext, Db: Database + DatabaseCommit, TrevmState> fmt::Debug for Trevm<'_, Ext, Db, TrevmState> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Trevm").finish_non_exhaustive()
    }
}

impl<'a, Ext, Db: Database + DatabaseCommit, TrevmState> AsRef<Evm<'a, Ext, Db>>
    for Trevm<'a, Ext, Db, TrevmState>
{
    fn as_ref(&self) -> &Evm<'a, Ext, Db> {
        &self.inner
    }
}

impl<'a, Ext, Db: Database + DatabaseCommit> From<Evm<'a, Ext, Db>> for EvmNeedsCfg<'a, Ext, Db> {
    fn from(inner: Evm<'a, Ext, Db>) -> Self {
        Self { inner: Box::new(inner), state: NeedsCfg::new() }
    }
}

// --- ALL STATES

impl<'a, Ext, Db: Database + DatabaseCommit, TrevmState> Trevm<'a, Ext, Db, TrevmState> {
    /// Get a reference to the current [`Evm`].
    pub fn inner(&self) -> &Evm<'a, Ext, Db> {
        self.as_ref()
    }

    /// Get a mutable reference to the current [`Evm`]. This should be used with
    /// caution, as modifying the EVM may lead to inconsistent Trevmstate or invalid
    /// execution.
    pub fn inner_mut_unchecked(&mut self) -> &mut Evm<'a, Ext, Db> {
        &mut self.inner
    }

    /// Destructure the [`Trevm`] into its parts.
    pub fn into_inner(self) -> Box<Evm<'a, Ext, Db>> {
        self.inner
    }

    /// Get the id of the currently running hardfork spec. Convenience function
    /// calling [`Evm::spec_id`].
    pub fn spec_id(&self) -> SpecId {
        self.inner.spec_id()
    }

    /// Set the [SpecId], modifying the EVM handlers accordingly. This function
    /// should be called at hardfork boundaries when running multi-block trevm
    /// flows.
    pub fn set_spec_id(&mut self, spec_id: SpecId) {
        self.inner.modify_spec_id(spec_id)
    }

    /// Run a closure with a different [SpecId], then restore the previous
    /// setting.
    pub fn with_spec_id<F, NewState>(
        mut self,
        spec_id: SpecId,
        f: F,
    ) -> Trevm<'a, Ext, Db, NewState>
    where
        F: FnOnce(Self) -> Trevm<'a, Ext, Db, NewState>,
    {
        let old = self.spec_id();
        self.set_spec_id(spec_id);
        let mut this = f(self);
        this.set_spec_id(old);
        this
    }

    /// Convert self into [`EvmErrored`] by supplying an error
    pub fn errored<E>(self, error: E) -> EvmErrored<'a, Ext, Db, E> {
        EvmErrored { inner: self.inner, state: ErroredState { error } }
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

    /// Apply [`StateOverride`]s to the current state. Errors if the overrides
    /// contain invalid bytecode.
    pub fn apply_state_overrides(
        mut self,
        overrides: &StateOverride,
    ) -> Result<Self, EVMError<Db::Error>> {
        for (address, account_override) in overrides {
            if let Some(balance) = account_override.balance {
                self.inner.set_balance(*address, balance).map_err(EVMError::Database)?;
            }
            if let Some(nonce) = account_override.nonce {
                self.inner.set_nonce(*address, nonce).map_err(EVMError::Database)?;
            }
            if let Some(code) = account_override.code.as_ref() {
                self.inner
                    .set_bytecode(
                        *address,
                        Bytecode::new_raw_checked(code.clone())
                            .map_err(|_| EVMError::Custom("Invalid bytecode".to_string()))?,
                    )
                    .map_err(EVMError::Database)?;
            }
            if let Some(state) = account_override.state.as_ref() {
                for (slot, value) in state {
                    self.inner
                        .set_storage(
                            *address,
                            U256::from_be_bytes((*slot).into()),
                            U256::from_be_bytes((*value).into()),
                        )
                        .map_err(EVMError::Database)?;
                }
            }
        }
        Ok(self)
    }

    /// Apply [`StateOverride`]s to the current state, if they are provided.
    pub fn maybe_apply_state_overrides(
        self,
        overrides: Option<&StateOverride>,
    ) -> Result<Self, EVMError<Db::Error>> {
        if let Some(overrides) = overrides {
            self.apply_state_overrides(overrides)
        } else {
            Ok(self)
        }
    }
}

impl<Ext, Db: Database + DatabaseCommit + DatabaseRef, TrevmState> Trevm<'_, Ext, Db, TrevmState> {
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

impl<Ext, Db: Database<Error = Infallible> + DatabaseCommit, TrevmState>
    Trevm<'_, Ext, Db, TrevmState>
{
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

impl<
        Ext,
        Db: Database<Error = Infallible> + DatabaseRef<Error = Infallible> + DatabaseCommit,
        TrevmState,
    > Trevm<'_, Ext, Db, TrevmState>
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

impl<Ext, Db: Database + DatabaseCommit, TrevmState> Trevm<'_, Ext, Db, TrevmState> {
    /// Commit a set of state changes to the database. This is a low-level API,
    /// and is not intended for general use. Prefer executing a transaction.
    pub fn commit_unchecked(&mut self, state: EvmState) {
        self.inner.db_mut().commit(state);
    }

    /// Modify an account with a closure and commit the modified account. This
    /// is a low-level API, and is not intended for general use.
    pub fn try_modify_account_unchecked<F: FnOnce(&mut AccountInfo)>(
        &mut self,
        address: Address,
        f: F,
    ) -> Result<AccountInfo, Db::Error> {
        self.inner.modify_account(address, f)
    }

    /// Set the nonce of an account, returning the previous nonce. This is a
    /// low-level API, and is not intended for general use.
    pub fn try_set_nonce_unchecked(
        &mut self,
        address: Address,
        nonce: u64,
    ) -> Result<u64, Db::Error> {
        self.inner.set_nonce(address, nonce)
    }

    /// Increment the nonce of an account, returning the previous nonce. This is
    /// a low-level API, and is not intended for general use.
    ///
    /// If the nonce is already at the maximum value, it will not be
    /// incremented.
    pub fn try_increment_nonce_unchecked(&mut self, address: Address) -> Result<u64, Db::Error> {
        self.inner.increment_nonce(address)
    }

    /// Decrement the nonce of an account, returning the previous nonce. This is
    /// a low-level API, and is not intended for general use.
    ///
    /// If the nonce is already 0, it will not be decremented.
    pub fn try_decrement_nonce_unchecked(&mut self, address: Address) -> Result<u64, Db::Error> {
        self.inner.decrement_nonce(address)
    }

    /// Set the EVM storage at a slot. This is a low-level API, and is not
    /// intended for general use.
    pub fn try_set_storage_unchecked(
        &mut self,
        address: Address,
        slot: U256,
        value: U256,
    ) -> Result<U256, Db::Error> {
        self.inner.set_storage(address, slot, value)
    }

    /// Set the bytecode at a specific address, returning the previous bytecode
    /// at that address. This is a low-level API, and is not intended for
    /// general use.
    pub fn try_set_bytecode_unchecked(
        &mut self,
        address: Address,
        bytecode: Bytecode,
    ) -> Result<Option<Bytecode>, Db::Error> {
        self.inner.set_bytecode(address, bytecode)
    }

    /// Increase the balance of an account. Returns the previous balance. This
    /// is a low-level API, and is not intended for general use.
    ///
    /// If this would cause an overflow, the balance will be increased to the
    /// maximum value.
    pub fn try_increase_balance_unchecked(
        &mut self,
        address: Address,
        amount: U256,
    ) -> Result<U256, Db::Error> {
        self.inner.increase_balance(address, amount)
    }

    /// Decrease the balance of an account. Returns the previous balance. This
    /// is a low-level API, and is not intended for general use.
    ///
    /// If this would cause an underflow, the balance will be decreased to 0.
    pub fn try_decrease_balance_unchecked(
        &mut self,
        address: Address,
        amount: U256,
    ) -> Result<U256, Db::Error> {
        self.inner.decrease_balance(address, amount)
    }

    /// Set the balance of an account. Returns the previous balance. This is a
    /// low-level API, and is not intended for general use.
    pub fn try_set_balance_unchecked(
        &mut self,
        address: Address,
        amount: U256,
    ) -> Result<U256, Db::Error> {
        self.inner.set_balance(address, amount)
    }
}

impl<Ext, Db: Database<Error = Infallible> + DatabaseCommit, TrevmState>
    Trevm<'_, Ext, Db, TrevmState>
{
    /// Modify an account with a closure and commit the modified account. This
    /// is a low-level API, and is not intended for general use.
    pub fn modify_account_unchecked(
        &mut self,
        address: Address,
        f: impl FnOnce(&mut AccountInfo),
    ) -> AccountInfo {
        self.try_modify_account_unchecked(address, f).expect("infallible")
    }

    /// Set the nonce of an account, returning the previous nonce. This is a
    /// low-level API, and is not intended for general use.
    pub fn set_nonce_unchecked(&mut self, address: Address, nonce: u64) -> u64 {
        self.try_set_nonce_unchecked(address, nonce).expect("infallible")
    }

    /// Increment the nonce of an account, returning the previous nonce. This is
    /// a low-level API, and is not intended for general use.
    ///
    /// If this would cause the nonce to overflow, the nonce will be set to the
    /// maximum value.
    pub fn increment_nonce_unchecked(&mut self, address: Address) -> u64 {
        self.try_increment_nonce_unchecked(address).expect("infallible")
    }

    /// Decrement the nonce of an account, returning the previous nonce. This is
    /// a low-level API, and is not intended for general use.
    ///
    /// If this would cause the nonce to underflow, the nonce will be set to 0.
    pub fn decrement_nonce_unchecked(&mut self, address: Address) -> u64 {
        self.try_decrement_nonce_unchecked(address).expect("infallible")
    }

    /// Set the EVM storage at a slot. This is a low-level API, and is not
    /// intended for general use.
    pub fn set_storage_unchecked(&mut self, address: Address, slot: U256, value: U256) -> U256 {
        self.try_set_storage_unchecked(address, slot, value).expect("infallible")
    }

    /// Set the bytecode at a specific address, returning the previous bytecode
    /// at that address. This is a low-level API, and is not intended for
    /// general use.
    pub fn set_bytecode_unchecked(
        &mut self,
        address: Address,
        bytecode: Bytecode,
    ) -> Option<Bytecode> {
        self.try_set_bytecode_unchecked(address, bytecode).expect("infallible")
    }

    /// Increase the balance of an account. Returns the previous balance. This
    /// is a low-level API, and is not intended for general use.
    pub fn increase_balance_unchecked(&mut self, address: Address, amount: U256) -> U256 {
        self.try_increase_balance_unchecked(address, amount).expect("infallible")
    }

    /// Decrease the balance of an account. Returns the previous balance. This
    /// is a low-level API, and is not intended for general use.
    pub fn decrease_balance_unchecked(&mut self, address: Address, amount: U256) -> U256 {
        self.try_decrease_balance_unchecked(address, amount).expect("infallible")
    }

    /// Set the balance of an account. Returns the previous balance. This is a
    /// low-level API, and is not intended for general use.
    pub fn set_balance_unchecked(&mut self, address: Address, amount: U256) -> U256 {
        self.try_set_balance_unchecked(address, amount).expect("infallible")
    }
}

// --- ALL STATES, WITH State<Db>

impl<Ext, Db: Database + DatabaseCommit, TrevmState> Trevm<'_, Ext, State<Db>, TrevmState> {
    /// Set the [EIP-161] state clear flag, activated in the Spurious Dragon
    /// hardfork.
    pub fn set_state_clear_flag(&mut self, flag: bool) {
        self.inner.db_mut().set_state_clear_flag(flag)
    }
}

// --- NEEDS CFG

impl<'a, Ext, Db: Database + DatabaseCommit> EvmNeedsCfg<'a, Ext, Db> {
    /// Fill the configuration environment.
    pub fn fill_cfg<T: Cfg>(mut self, filler: &T) -> EvmNeedsBlock<'a, Ext, Db> {
        filler.fill_cfg(&mut self.inner);
        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { core::mem::transmute(self) }
    }
}

// --- HAS CFG

impl<'a, Ext, Db: Database + DatabaseCommit, TrevmState: HasCfg> Trevm<'a, Ext, Db, TrevmState> {
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

    /// Run a function with the provided configuration, then restore the
    /// previous configuration. This will not affect the block and tx, if those
    /// have been filled.
    pub fn with_cfg<C, F, NewState>(mut self, cfg: &C, f: F) -> Trevm<'a, Ext, Db, NewState>
    where
        C: Cfg,
        F: FnOnce(Self) -> Trevm<'a, Ext, Db, NewState>,
        NewState: HasCfg,
    {
        let previous = self.inner.cfg_mut().clone();
        cfg.fill_cfg_env(self.inner.cfg_mut());
        let mut this = f(self);
        *this.inner.cfg_mut() = previous;
        this
    }

    /// Run a fallible function with the provided configuration, then restore the
    /// previous configuration. This will not affect the block and tx, if those
    /// have been filled.
    pub fn try_with_cfg<C, F, NewState, E>(
        mut self,
        cfg: &C,
        f: F,
    ) -> Result<Trevm<'a, Ext, Db, NewState>, EvmErrored<'a, Ext, Db, E>>
    where
        C: Cfg,
        F: FnOnce(Self) -> Result<Trevm<'a, Ext, Db, NewState>, EvmErrored<'a, Ext, Db, E>>,
        NewState: HasCfg,
    {
        let previous = self.inner.cfg_mut().clone();
        cfg.fill_cfg_env(self.inner.cfg_mut());
        match f(self) {
            Ok(mut evm) => {
                *evm.inner.cfg_mut() = previous;
                Ok(evm)
            }
            Err(mut evm) => {
                *evm.inner.cfg_mut() = previous;
                Err(evm)
            }
        }
    }

    /// Set the KZG settings used for point evaluation precompiles. By default
    /// this is set to the settings used in the Ethereum mainnet.
    ///
    /// This is a low-level API, and is not intended for general use.
    #[cfg(feature = "c-kzg")]
    pub fn set_kzg_settings(
        &mut self,
        settings: revm::primitives::EnvKzgSettings,
    ) -> revm::primitives::EnvKzgSettings {
        let cfg = self.inner.cfg_mut();
        core::mem::replace(&mut cfg.kzg_settings, settings)
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
        core::mem::replace(&mut cfg.memory_limit, new_limit)
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

impl<'a, Ext, Db: Database + DatabaseCommit> EvmNeedsBlock<'a, Ext, Db> {
    /// Open a block, apply some logic, and return the EVM ready for the next
    /// block.
    pub fn drive_block<D>(self, driver: &mut D) -> DriveBlockResult<'a, Ext, Db, D>
    where
        D: BlockDriver<Ext>,
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
    pub fn drive_chain<D>(self, driver: &mut D) -> DriveChainResult<'a, Ext, Db, D>
    where
        D: ChainDriver<Ext>,
    {
        let block_count = driver.blocks().len();

        let mut trevm = self
            .drive_block(&mut driver.blocks()[0])
            .map_err(EvmErrored::err_into::<<D as ChainDriver<Ext>>::Error<Db>>)?;

        if let Err(e) = driver.interblock(&trevm, 0) {
            return Err(trevm.errored(e));
        }

        for i in 1..block_count {
            trevm = {
                let trevm = trevm
                    .drive_block(&mut driver.blocks()[i])
                    .map_err(EvmErrored::err_into::<<D as ChainDriver<Ext>>::Error<Db>>)?;
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
    pub fn fill_block<B: Block>(mut self, filler: &B) -> EvmNeedsTx<'a, Ext, Db> {
        filler.fill_block(self.inner_mut_unchecked());
        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { core::mem::transmute(self) }
    }
}

// --- HAS BLOCK

impl<'a, Ext, Db: Database + DatabaseCommit, TrevmState: HasBlock> Trevm<'a, Ext, Db, TrevmState> {
    /// Get a reference to the current block environment.
    pub fn block(&self) -> &BlockEnv {
        self.inner.block()
    }

    /// Get the current block gas limit.
    pub fn block_gas_limit(&self) -> U256 {
        self.block().gas_limit
    }

    /// Get the current block number.
    pub fn block_number(&self) -> U256 {
        self.block().number
    }

    /// Get the current block timestamp.
    pub fn block_timestamp(&self) -> U256 {
        self.block().timestamp
    }

    /// Get the block beneficiary address.
    pub fn beneficiary(&self) -> Address {
        self.block().coinbase
    }

    /// Run a function with the provided block, then restore the previous block.
    pub fn with_block<B, F, NewState>(mut self, b: &B, f: F) -> Trevm<'a, Ext, Db, NewState>
    where
        B: Block,
        F: FnOnce(Self) -> Trevm<'a, Ext, Db, NewState>,
        NewState: HasBlock,
    {
        let previous = self.inner.block_mut().clone();
        b.fill_block_env(self.inner.block_mut());
        let mut this = f(self);
        *this.inner.block_mut() = previous;
        this
    }

    /// Run a fallible function with the provided block, then restore the previous block.
    pub fn try_with_block<B, F, NewState, E>(
        mut self,
        b: &B,
        f: F,
    ) -> Result<Trevm<'a, Ext, Db, NewState>, EvmErrored<'a, Ext, Db, E>>
    where
        F: FnOnce(Self) -> Result<Trevm<'a, Ext, Db, NewState>, EvmErrored<'a, Ext, Db, E>>,
        B: Block,
        NewState: HasBlock,
    {
        let previous = self.inner.block_mut().clone();
        b.fill_block_env(self.inner.block_mut());
        match f(self) {
            Ok(mut evm) => {
                *evm.inner.block_mut() = previous;
                Ok(evm)
            }
            Err(mut evm) => {
                *evm.inner.block_mut() = previous;
                Err(evm)
            }
        }
    }
}

// --- Needs Block with State<Db>

impl<Ext, Db: Database> EvmNeedsBlock<'_, Ext, State<Db>> {
    /// Finish execution and return the outputs.
    ///
    /// If the State has not been built with
    /// [revm::StateBuilder::with_bundle_update] then the returned
    /// [`BundleState`] will be meaningless.
    ///
    /// See [`State::merge_transitions`] and [`State::take_bundle`].
    pub fn finish(self) -> BundleState {
        let Self { inner: mut evm, .. } = self;
        evm.db_mut().merge_transitions(BundleRetention::Reverts);
        let bundle = evm.db_mut().take_bundle();

        bundle
    }
}

// --- NEEDS TX

impl<'a, Ext, Db: Database + DatabaseCommit> EvmNeedsTx<'a, Ext, Db> {
    /// Close the current block, returning the EVM ready for the next block.
    pub fn close_block(self) -> EvmNeedsBlock<'a, Ext, Db> {
        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { core::mem::transmute(self) }
    }

    /// Drive a bundle to completion, apply some post-bundle logic, and return the
    /// EVM ready for the next bundle or tx.
    pub fn drive_bundle<D>(self, driver: &mut D) -> DriveBundleResult<'a, Ext, Db, D>
    where
        D: BundleDriver<Ext>,
    {
        let trevm = driver.run_bundle(self)?;

        match driver.post_bundle(&trevm) {
            Ok(_) => Ok(trevm),
            Err(e) => Err(trevm.errored(e)),
        }
    }

    /// Fill the transaction environment.
    pub fn fill_tx<T: Tx>(mut self, filler: &T) -> EvmReady<'a, Ext, Db> {
        filler.fill_tx(&mut self.inner);
        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { core::mem::transmute(self) }
    }

    /// Execute a transaction. Shortcut for `fill_tx(tx).run_tx()`.
    pub fn run_tx<T: Tx>(
        self,
        filler: &T,
    ) -> Result<EvmTransacted<'a, Ext, Db>, EvmErrored<'a, Ext, Db>> {
        self.fill_tx(filler).run()
    }

    /// Estimate the gas cost of a transaction. Shortcut for `fill_tx(tx).
    /// estimate()`. Returns an [`EstimationResult`] and the EVM populated with
    /// the transaction.
    pub fn estimate_tx_gas<T: Tx>(
        self,
        filler: &T,
    ) -> Result<(EstimationResult, EvmReady<'a, Ext, Db>), EvmErrored<'a, Ext, Db>> {
        self.fill_tx(filler).estimate_gas()
    }
}

// --- HAS TX

impl<'a, Ext, Db: Database + DatabaseCommit, TrevmState: HasTx> Trevm<'a, Ext, Db, TrevmState> {
    /// Convenience function to use the estimator to fill both Cfg and Tx, and
    /// run a fallible function.
    fn try_with_estimator<E>(
        self,
        estimator: &GasEstimationFiller,
        f: impl FnOnce(Self) -> Result<Self, EvmErrored<'a, Ext, Db, E>>,
    ) -> Result<Self, EvmErrored<'a, Ext, Db, E>> {
        self.try_with_cfg(estimator, |this| this.try_with_tx(estimator, f))
    }

    /// Get a reference to the loaded tx env that will be executed.
    pub fn tx(&self) -> &TxEnv {
        self.inner.tx()
    }
    /// True if the transaction is a simple transfer.
    pub fn is_transfer(&self) -> bool {
        self.inner.tx().data.is_empty() && self.to().is_call()
    }

    /// True if the transaction is a contract creation.
    pub fn is_create(&self) -> bool {
        self.to().is_create()
    }

    /// Get a reference to the transaction input data, which will be used as
    /// calldata or initcode during EVM execution.
    pub fn data(&self) -> &Bytes {
        &self.tx().data
    }

    /// Read the target of the transaction.
    pub fn to(&self) -> TxKind {
        self.tx().transact_to
    }

    /// Read the value in wei of the transaction.
    pub fn value(&self) -> U256 {
        self.tx().value
    }

    /// Get the gas limit of the loaded transaction.
    pub fn gas_limit(&self) -> u64 {
        self.tx().gas_limit
    }

    /// Get the gas price of the loaded transaction.
    pub fn gas_price(&self) -> U256 {
        self.tx().gas_price
    }

    /// Get the address of the caller.
    pub fn caller(&self) -> Address {
        self.tx().caller
    }

    /// Get the account of the caller. Error if the DB errors.
    pub fn caller_account(&mut self) -> Result<AccountInfo, EVMError<Db::Error>> {
        self.try_read_account(self.caller())
            .map(Option::unwrap_or_default)
            .map_err(EVMError::Database)
    }

    /// Get the address of the callee. `None` if `Self::is_create` is true.
    pub fn callee(&self) -> Option<Address> {
        self.to().into()
    }

    /// Get the account of the callee.
    ///
    /// Returns as follows:
    /// - if `Self::is_create` is true, `Ok(None)`
    /// - if the callee account does not exist, `Ok(AccountInfo::default())`
    /// - if the DB errors, `Err(EVMError::Database(err))`
    pub fn callee_account(&mut self) -> Result<Option<AccountInfo>, EVMError<Db::Error>> {
        self.callee().map_or(Ok(None), |addr| {
            self.try_read_account(addr)
                .map(Option::unwrap_or_default)
                .map(Some)
                .map_err(EVMError::Database)
        })
    }

    /// Get the account of the callee. `None` if `Self::is_create` is true,
    /// error if the DB errors.
    pub fn callee_account_ref(&self) -> Result<Option<AccountInfo>, <Db as DatabaseRef>::Error>
    where
        Db: DatabaseRef,
    {
        self.callee().map_or(Ok(None), |addr| self.try_read_account_ref(addr))
    }

    /// Run a function with the provided transaction, then restore the previous
    /// transaction.
    pub fn with_tx<T, F, NewState>(mut self, t: &T, f: F) -> Trevm<'a, Ext, Db, NewState>
    where
        T: Tx,
        F: FnOnce(Self) -> Trevm<'a, Ext, Db, NewState>,
        NewState: HasTx,
    {
        let previous = self.inner.tx_mut().clone();
        t.fill_tx_env(self.inner.tx_mut());
        let mut this = f(self);
        *this.inner.tx_mut() = previous;
        this
    }

    /// Run a fallible function with the provided transaction, then restore the
    /// previous transaction.
    pub fn try_with_tx<T, F, NewState, E>(
        mut self,
        t: &T,
        f: F,
    ) -> Result<Trevm<'a, Ext, Db, NewState>, EvmErrored<'a, Ext, Db, E>>
    where
        T: Tx,
        F: FnOnce(Self) -> Result<Trevm<'a, Ext, Db, NewState>, EvmErrored<'a, Ext, Db, E>>,
        NewState: HasTx,
    {
        let previous = self.inner.tx_mut().clone();
        t.fill_tx_env(self.inner.tx_mut());
        match f(self) {
            Ok(mut evm) => {
                *evm.inner.tx_mut() = previous;
                Ok(evm)
            }
            Err(mut evm) => {
                *evm.inner.tx_mut() = previous;
                Err(evm)
            }
        }
    }

    /// Return the maximum gas that the caller can purchase. This is the balance
    /// of the caller divided by the gas price.
    pub fn gas_allowance(&mut self) -> Result<u64, EVMError<Db::Error>> {
        // Avoid DB read if gas price is zero
        let gas_price = self.gas_price();
        if gas_price.is_zero() {
            return Ok(u64::MAX);
        }

        let balance = self.try_read_balance(self.caller()).map_err(EVMError::Database)?;
        Ok((balance / gas_price).saturating_to())
    }
}

// -- HAS TX with State<Db>

impl<Ext, Db: Database> EvmNeedsTx<'_, Ext, State<Db>> {
    /// Apply block overrides to the current block.
    ///
    /// Note that this is NOT reversible. The overrides are applied directly to
    /// the underlying state and these changes cannot be removed. If it is
    /// important that you have access to the pre-change state, you should wrap
    /// the existing DB in a new [`State`] and apply the overrides to that.
    pub fn apply_block_overrides(mut self, overrides: &BlockOverrides) -> Self {
        overrides.fill_block(&mut self.inner);

        if let Some(hashes) = &overrides.block_hash {
            self.inner.db_mut().block_hashes.extend(hashes)
        }

        self
    }

    /// Apply block overrides to the current block, if they are provided.
    ///
    /// Note that this is NOT reversible. The overrides are applied directly to
    /// the underlying state and these changes cannot be removed. If it is
    /// important that you have access to the pre-change state, you should wrap
    /// the existing DB in a new [`State`] and apply the overrides to that.
    pub fn maybe_apply_block_overrides(self, overrides: Option<&BlockOverrides>) -> Self {
        if let Some(overrides) = overrides {
            self.apply_block_overrides(overrides)
        } else {
            self
        }
    }
}

// --- READY

impl<'a, Ext, Db: Database + DatabaseCommit> EvmReady<'a, Ext, Db> {
    /// Clear the current transaction environment.
    pub fn clear_tx(self) -> EvmNeedsTx<'a, Ext, Db> {
        // NB: we do not clear the tx env here, as we may read it during post-tx
        // logic in a block driver

        // SAFETY: Same size and repr. Only phantomdata type changes
        unsafe { core::mem::transmute(self) }
    }

    /// Execute the loaded transaction. This is a wrapper around
    /// [`Evm::transact`] and produces either [`EvmTransacted`] or
    /// [`EvmErrored`].
    pub fn run(mut self) -> Result<EvmTransacted<'a, Ext, Db>, EvmErrored<'a, Ext, Db>> {
        let result = self.inner.transact();

        let Trevm { inner, .. } = self;

        match result {
            Ok(result) => Ok(Trevm { inner, state: TransactedState { result } }),
            Err(error) => Err(EvmErrored { inner, state: ErroredState { error } }),
        }
    }

    /// Estimate gas for a simple transfer. This will
    /// - Check that the transaction has no input data.
    /// - Check that the target is not a `create`.
    /// - Check that the target is not a contract.
    /// - Return the minimum gas required for the transfer.
    fn estimate_gas_simple_transfer(&mut self) -> Result<Option<()>, EVMError<Db::Error>> {
        if !self.is_transfer() {
            return Ok(None);
        }

        // Shortcut if the tx is create, otherwise read the account
        let Some(acc) = self.callee_account()? else { return Ok(None) };

        // If the code hash is not empty, then the target is a contract
        if acc.code_hash != KECCAK_EMPTY {
            return Ok(None);
        }

        // If the target is not a contract, then the gas is the minimum gas.
        Ok(Some(()))
    }

    /// Convenience function to simplify nesting of [`Self::estimate_gas`].
    fn run_estimate(
        self,
        estimator: &GasEstimationFiller,
    ) -> Result<(EstimationResult, Self), EvmErrored<'a, Ext, Db>> {
        let mut estimation = None;

        let this = self.try_with_estimator(estimator, |this| match this.run() {
            Ok(trevm) => {
                let (e, t) = trevm.take_estimation();

                estimation = Some(e);
                Ok(t)
            }
            Err(err) => Err(err),
        })?;

        Ok((estimation.expect("definitely exists if not shortcut returned"), this))
    }

    /// Implements gas estimation. This will output an estimate of the minimum
    /// amount of gas that the transaction will consume, calculated via
    /// iterated simulation.
    ///
    /// In the worst case this will perform a binary search, resulting in
    /// `O(log(n))` simulations.
    pub fn estimate_gas(mut self) -> Result<(EstimationResult, Self), EvmErrored<'a, Ext, Db>> {
        if unwrap_or_trevm_err!(self.estimate_gas_simple_transfer(), self).is_some() {
            return Ok((EstimationResult::basic_transfer_success(), self));
        }

        // We shrink the gas limit to 64 bits, as using more than 18 quintillion
        // gas in a block is not likely.
        let initial_limit = self.gas_limit();
        let block_gas_limit = self.block_gas_limit().saturating_to::<u64>();

        // The highest possible gas is the minimum of the initial limit and the
        // block gas limit.
        let allowance = unwrap_or_trevm_err!(self.gas_allowance(), self);
        let highest_possible_gas = std::cmp::min(initial_limit, block_gas_limit);
        let highest_possible_gas = std::cmp::min(highest_possible_gas, allowance);

        // Run an estimate with the max gas limit.
        let estimator = GasEstimationFiller::from(highest_possible_gas);
        let (mut estimate, mut trevm) = self.run_estimate(&estimator)?;

        // If it failed, no amount of gas is likely to work, so we shortcut
        // return.
        if estimate.is_failure() {
            return Ok((estimate, trevm));
        }

        // Now we know that it succeeds at _some_ gas limit. We can now binary
        // search.
        let mut gas_used = estimate.gas_estimation().expect("checked is_failure");
        let gas_refunded = estimate.gas_refunded().expect("checked is_failure");

        // Set our binary search bounds.
        let mut search_max = highest_possible_gas;
        let mut search_min = std::cmp::max(gas_used - 1, MIN_TRANSACTION_GAS);

        // NB: This is a heuristic adopted from geth and reth
        // https://github.com/ethereum/go-ethereum/blob/a5a4fa7032bb248f5a7c40f4e8df2b131c4186a4/eth/gasestimator/gasestimator.go#L132-L135
        // NB: 64 / 63 is due to Ethereum's gas-forwarding rules. Each call
        // frame can forward only 63/64 of the gas it has when it makes a new
        // frame.
        let first_search = gas_used + gas_refunded + CALL_STIPEND * 64 / 63;
        if first_search < search_max {
            let estimator = GasEstimationFiller::from(first_search);
            (estimate, trevm) = trevm.run_estimate(&estimator)?;
            // If the halt error propagates, we can shortcut return, as it
            // means that a non-gas-dynamic halt occurred.
            if let Err(e) =
                estimate.adjust_binary_search_range(first_search, &mut search_max, &mut search_min)
            {
                return Ok((e, trevm));
            }
            gas_used = estimate.gas_used();
        }

        // This is a heuristic adopted from reth
        // Pick a point that's close to the estimated gas
        let mut needle = std::cmp::min(gas_used * 3, (search_max + search_min) / 2);

        // Binary search
        while search_max.saturating_sub(search_min) > 1 {
            // This is a heuristic adopted from reth
            // An estimation error is allowed once the current gas limit range
            // used in the binary search is small enough (less than 1.5% of the
            // highest gas limit)
            // <https://github.com/ethereum/go-ethereum/blob/a5a4fa7032bb248f5a7c40f4e8df2b131c4186
            if ((search_max - search_min) as f64 / search_max as f64) < 0.015 {
                break;
            };

            // If the halt error propagates, we can shortcut return, as it
            // means that a non-gas-dynamic halt occurred.
            let estimator = GasEstimationFiller::from(needle);
            (estimate, trevm) = trevm.run_estimate(&estimator)?;
            if let Err(e) =
                estimate.adjust_binary_search_range(needle, &mut search_max, &mut search_min)
            {
                return Ok((e, trevm));
            }

            // NB: 2 is the binary part of the binary search :)
            needle = (search_max + search_min) / 2;
        }

        Ok((estimate, trevm))

        // Ok((estimator.gas_limit, trevm))
    }
}

// --- ERRORED

impl<'a, Ext, Db: Database + DatabaseCommit, E> EvmErrored<'a, Ext, Db, E> {
    /// Get a reference to the error.
    pub const fn error(&self) -> &E {
        &self.state.error
    }

    /// Inspect the error with a closure.
    pub fn inspect_err<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&E) -> T,
    {
        f(self.error())
    }

    /// Discard the error and return the EVM.
    pub fn discard_error(self) -> EvmNeedsTx<'a, Ext, Db> {
        Trevm { inner: self.inner, state: NeedsTx::new() }
    }

    /// Convert the error into an [`EVMError`].
    pub fn into_error(self) -> E {
        self.state.error
    }

    /// Reset the EVM, returning the error and the EVM ready for the next
    /// transaction.
    pub fn take_err(self) -> (E, EvmNeedsTx<'a, Ext, Db>) {
        let Trevm { inner, state: ErroredState { error } } = self;
        (error, Trevm { inner, state: NeedsTx::new() })
    }

    /// Transform the error into a new error type.
    pub fn err_into<NewErr: From<E>>(self) -> EvmErrored<'a, Ext, Db, NewErr> {
        self.map_err(Into::into)
    }

    /// Map the error to a new error type.
    pub fn map_err<F, NewErr>(self, f: F) -> EvmErrored<'a, Ext, Db, NewErr>
    where
        F: FnOnce(E) -> NewErr,
    {
        Trevm { inner: self.inner, state: ErroredState { error: f(self.state.error) } }
    }
}

impl<'a, Ext, Db: Database + DatabaseCommit> EvmErrored<'a, Ext, Db> {
    /// Check if the error is a transaction error. This is provided as a
    /// convenience function for common cases, as Transaction errors should
    /// usually be discarded.
    pub const fn is_transaction_error(&self) -> bool {
        matches!(self.state.error, EVMError::Transaction(_))
    }

    /// Fallible cast to a [`InvalidTransaction`].
    pub const fn as_transaction_error(&self) -> Option<&InvalidTransaction> {
        match &self.state.error {
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

// --- TRANSACTED

impl<Ext, Db: Database + DatabaseCommit> AsRef<ResultAndState> for EvmTransacted<'_, Ext, Db> {
    fn as_ref(&self) -> &ResultAndState {
        &self.state.result
    }
}

impl<Ext, Db: Database + DatabaseCommit> AsRef<ExecutionResult> for EvmTransacted<'_, Ext, Db> {
    fn as_ref(&self) -> &ExecutionResult {
        &self.state.result.result
    }
}

impl<'a, Ext, Db: Database + DatabaseCommit> EvmTransacted<'a, Ext, Db> {
    /// Get a reference to the result.
    pub fn result(&self) -> &ExecutionResult {
        self.as_ref()
    }

    /// Get a mutable reference to the result. Modification of the result is
    /// discouraged, as it may lead to inconsistent state.
    ///
    /// This is primarily intended for use in [`SystemTx`] execution.
    ///
    /// [`SystemTx`]: crate::system::SystemTx
    pub fn result_mut_unchecked(&mut self) -> &mut ExecutionResult {
        &mut self.state.result.result
    }

    /// Get a reference to the state.
    pub const fn state(&self) -> &EvmState {
        &self.state.result.state
    }

    /// Get a mutable reference to the state. Modification of the state is
    /// discouraged, as it may lead to inconsistent state.
    pub fn state_mut_unchecked(&mut self) -> &mut EvmState {
        &mut self.state.result.state
    }

    /// Get a reference to the result and state.
    pub fn result_and_state(&self) -> &ResultAndState {
        self.as_ref()
    }

    /// Get a mutable reference to the result and state. Modification of the
    /// result and state is discouraged, as it may lead to inconsistent state.
    ///
    /// This is primarily intended for use in [`SystemTx`] execution.
    ///
    /// [`SystemTx`]: crate::system::SystemTx
    pub fn result_and_state_mut_unchecked(&mut self) -> &mut ResultAndState {
        &mut self.state.result
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
        self.state.result.result.gas_used()
    }

    /// Discard the state changes and return the EVM.
    pub fn reject(self) -> EvmNeedsTx<'a, Ext, Db> {
        Trevm { inner: self.inner, state: NeedsTx::new() }
    }

    /// Take the [`ResultAndState`] and return the EVM.
    pub fn into_result_and_state(self) -> ResultAndState {
        self.state.result
    }

    /// Take the [`ResultAndState`] and return the EVM.
    pub fn take_result_and_state(self) -> (ResultAndState, EvmNeedsTx<'a, Ext, Db>) {
        let Trevm { inner, state: TransactedState { result } } = self;
        (result, Trevm { inner, state: NeedsTx::new() })
    }

    /// Take the [`ExecutionResult`], discard the [`EvmState`] and return the
    /// EVM.
    pub fn take_result(self) -> (ExecutionResult, EvmNeedsTx<'a, Ext, Db>) {
        let Trevm { inner, state: TransactedState { result } } = self;
        (result.result, Trevm { inner, state: NeedsTx::new() })
    }

    /// Accept the state changes, commiting them to the database, and return the
    /// EVM with the [`ExecutionResult`].
    pub fn accept(self) -> (ExecutionResult, EvmNeedsTx<'a, Ext, Db>) {
        let Trevm { mut inner, state: TransactedState { result } } = self;

        inner.db_mut().commit(result.state);

        (result.result, Trevm { inner, state: NeedsTx::new() })
    }

    /// Accept the state changes, commiting them to the database. Do not return
    /// the [`ExecutionResult.`]
    pub fn accept_state(self) -> EvmNeedsTx<'a, Ext, Db> {
        self.accept().1
    }

    /// Create an [`EstimationResult`] from the transaction [`ExecutionResult`].
    pub fn estimation(&self) -> EstimationResult {
        self.result().into()
    }

    /// Take the [`EstimationResult`] and return it and the EVM. This discards
    /// pending state changes.
    pub fn take_estimation(self) -> (EstimationResult, EvmReady<'a, Ext, Db>) {
        let estimation = self.estimation();
        (estimation, Trevm { inner: self.inner, state: Ready::new() })
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
