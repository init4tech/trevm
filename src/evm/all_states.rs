use crate::{
    db::{StateAcc, TryStateAcc},
    helpers::{Ctx, Evm, Instruction},
    inspectors::Layered,
    ErroredState, EvmErrored, EvmExtUnchecked, Trevm,
};
use alloy::{
    primitives::{Address, U256},
    rpc::types::state::StateOverride,
};
use core::convert::Infallible;
use revm::{
    bytecode::opcode::DIFFICULTY,
    context::{result::EVMError, Cfg as _, ContextTr},
    handler::EthPrecompiles,
    inspector::NoOpInspector,
    interpreter::instructions::block_info,
    primitives::hardfork::SpecId,
    state::{AccountInfo, Bytecode, EvmState},
    Database, DatabaseCommit, DatabaseRef, Inspector,
};

impl<Db, Insp, TrevmState> Trevm<Db, Insp, TrevmState>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    /// Get a reference to the current [`Evm`].
    ///
    /// [`Evm`]: revm::context::Evm
    pub fn inner(&self) -> &Evm<Db, Insp> {
        self.as_ref()
    }

    /// Get a mutable reference to the current [`Evm`]. This should be used with
    /// caution, as modifying the EVM may lead to inconsistent Trevmstate or
    /// invalid execution.
    ///
    /// [`Evm`]: revm::context::Evm
    pub fn inner_mut_unchecked(&mut self) -> &mut Evm<Db, Insp> {
        &mut self.inner
    }

    /// Destructure the [`Trevm`] into its inner EVM.
    pub fn into_inner(self) -> Box<Evm<Db, Insp>> {
        self.inner
    }

    /// Deconstruct the [`Trevm`] into the backing DB, dropping all other types.
    pub fn into_db(self) -> Db {
        self.inner.ctx.journaled_state.database
    }

    /// Get a reference to the inspector.
    pub fn inspector(&self) -> &Insp {
        &self.inner.inspector
    }

    /// Get a mutable reference to the inspector.
    pub fn inspector_mut(&mut self) -> &mut Insp {
        &mut self.inner.inspector
    }

    /// Replace the current inspector with a new inspector of the same type.
    pub fn replace_inspector(mut self, inspector: Insp) -> Self {
        *self.inspector_mut() = inspector;
        self
    }

    /// Layer a new inspector on top of the current one.
    pub fn layer_inspector<Insp2>(
        self,
        inspector: Insp2,
    ) -> Trevm<Db, Layered<Insp2, Insp>, TrevmState>
    where
        Insp2: Inspector<Ctx<Db>>,
    {
        let inner = Box::new(Evm {
            ctx: self.inner.ctx,
            inspector: Layered::new(inspector, self.inner.inspector),
            instruction: self.inner.instruction,
            precompiles: self.inner.precompiles,
            frame_stack: self.inner.frame_stack,
        });
        Trevm { inner, state: self.state }
    }

    /// Take the inspector out of the Trevm, replacing it with a
    /// [`NoOpInspector`].
    pub fn take_inspector(self) -> (Insp, Trevm<Db, NoOpInspector, TrevmState>) {
        let inspector = self.inner.inspector;
        let inner = Box::new(Evm {
            ctx: self.inner.ctx,
            inspector: NoOpInspector,
            instruction: self.inner.instruction,
            precompiles: self.inner.precompiles,
            frame_stack: self.inner.frame_stack,
        });
        (inspector, Trevm { inner, state: self.state })
    }

    /// Replace the current inspector with a new one, dropping the old one.
    pub fn set_inspector<Insp2>(self, inspector: Insp2) -> Trevm<Db, Insp2, TrevmState>
    where
        Insp2: Inspector<Ctx<Db>>,
    {
        let inner = Box::new(Evm {
            ctx: self.inner.ctx,
            inspector,
            instruction: self.inner.instruction,
            precompiles: self.inner.precompiles,
            frame_stack: self.inner.frame_stack,
        });
        Trevm { inner, state: self.state }
    }

    /// Run the closure with a different inspector, then restore the previous
    /// one.
    pub fn with_inspector<Insp2, F, NewState>(
        self,
        inspector: Insp2,
        f: F,
    ) -> Trevm<Db, Insp, NewState>
    where
        Insp2: Inspector<Ctx<Db>>,
        F: FnOnce(Trevm<Db, Insp2, TrevmState>) -> Trevm<Db, Insp2, NewState>,
    {
        let (old, this) = self.take_inspector();
        let this = f(this.set_inspector(inspector));
        this.set_inspector(old)
    }

    /// Run a fallible function with the provided inspector, then restore the
    /// previous inspector. If the function returns an error, it will be
    /// wrapped in an [`EvmErrored`] along with the current EVM state.
    pub fn try_with_inspector<F, Insp2, NewState, E>(
        self,
        inspector: Insp2,
        f: F,
    ) -> Result<Trevm<Db, Insp, NewState>, EvmErrored<Db, Insp, E>>
    where
        Insp2: Inspector<Ctx<Db>>,
        F: FnOnce(
            Trevm<Db, Insp2, TrevmState>,
        ) -> Result<Trevm<Db, Insp2, NewState>, EvmErrored<Db, Insp2, E>>,
    {
        let (previous, this) = self.take_inspector();
        let this = this.set_inspector(inspector);

        match f(this) {
            Ok(evm) => Ok(evm.set_inspector(previous)),
            Err(evm) => Err(evm.set_inspector(previous)),
        }
    }

    /// Get the id of the currently running hardfork spec.
    pub fn spec_id(&self) -> SpecId {
        self.inner.ctx.cfg().spec()
    }

    /// Set the [SpecId], modifying the EVM handlers accordingly. This function
    /// should be called at hardfork boundaries when running multi-block trevm
    /// flows.
    pub fn set_spec_id(&mut self, spec_id: SpecId) {
        self.inner.modify_cfg(|cfg| cfg.spec = spec_id);
    }

    /// Run a closure with a different [SpecId], then restore the previous
    /// setting.
    pub fn with_spec_id<F, NewState>(mut self, spec_id: SpecId, f: F) -> Trevm<Db, Insp, NewState>
    where
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
    {
        let old = self.spec_id();
        self.set_spec_id(spec_id);
        let mut this = f(self);
        this.set_spec_id(old);
        this
    }

    /// Convert self into [`EvmErrored`] by supplying an error
    pub fn errored<E>(self, error: E) -> EvmErrored<Db, Insp, E> {
        EvmErrored { inner: self.inner, state: ErroredState { error } }
    }

    /// Apply [`StateOverride`]s to the current state. Errors if the overrides
    /// contain invalid bytecode.
    pub fn apply_state_overrides(
        mut self,
        overrides: &StateOverride,
    ) -> Result<Self, EVMError<<Db as Database>::Error>>
    where
        Db: DatabaseCommit,
    {
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
    ) -> Result<Self, EVMError<<Db as Database>::Error>>
    where
        Db: DatabaseCommit,
    {
        if let Some(overrides) = overrides {
            self.apply_state_overrides(overrides)
        } else {
            Ok(self)
        }
    }

    /// Overide an opcode with a custom handler. Returns the previous
    /// instruction handler for the opcode.
    pub fn override_opcode(&mut self, opcode: u8, handler: Instruction<Db>) -> Instruction<Db> {
        std::mem::replace(&mut self.inner.instruction.instruction_table[opcode as usize], handler)
    }

    /// Disable an opcode by replacing it with unknown opcode behavior. This is
    /// a shortcut for [`Self::override_opcode`] with [`crate::helpers::forbidden`].
    pub fn disable_opcode(&mut self, opcode: u8) -> Instruction<Db> {
        self.override_opcode(opcode, crate::helpers::forbidden)
    }

    /// Run some closure with an opcode override, then restore the previous
    /// setting.
    pub fn with_opcode_override<F, NewState>(
        mut self,
        opcode: u8,
        handler: Instruction<Db>,
        f: F,
    ) -> Trevm<Db, Insp, NewState>
    where
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
    {
        let old = self.override_opcode(opcode, handler);
        self.inner.instruction.insert_instruction(opcode, handler);
        let mut this = f(self);
        this.override_opcode(opcode, old);
        this
    }

    /// Disable the prevrandao opcode, by replacing it with unknown opcode
    /// behavior. This is useful for block simulation, where the prevrandao
    /// opcode may produce incorrect results.
    pub fn disable_prevrandao(&mut self) -> Instruction<Db> {
        self.disable_opcode(DIFFICULTY)
    }

    /// Enable the prevrandao opcode. If the prevrandao opcode was not
    /// previously disabled or replaced, this will have no effect on behavior.
    pub fn enable_prevrandao(&mut self) -> Instruction<Db> {
        self.override_opcode(DIFFICULTY, block_info::difficulty)
    }

    /// Run some code with the prevrandao opcode disabled, then restore the
    /// previous setting. This is useful for block simulation, where the
    /// prevrandao opcode may produce incorrect results.
    pub fn without_prevrandao<F, NewState>(self, f: F) -> Trevm<Db, Insp, NewState>
    where
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
    {
        self.with_opcode_override(DIFFICULTY, crate::helpers::forbidden, f)
    }

    /// Set the precompiles for the EVM. This will replace the current
    /// precompiles with the provided ones.
    pub fn override_precompiles(&mut self, precompiles: EthPrecompiles) -> EthPrecompiles {
        std::mem::replace(&mut self.inner.precompiles, precompiles)
    }

    /// Run a closure with a different set of precompiles, then restore the
    /// previous setting.
    pub fn with_precompiles<F, NewState>(
        mut self,
        precompiles: EthPrecompiles,
        f: F,
    ) -> Trevm<Db, Insp, NewState>
    where
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
    {
        let old = self.override_precompiles(precompiles);
        let mut this = f(self);
        this.override_precompiles(old);
        this
    }
}

// Fallible DB Reads with &mut self
impl<Db, Insp, TrevmState> Trevm<Db, Insp, TrevmState>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    /// Get the current account info for a specific address.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn try_read_account(
        &mut self,
        address: Address,
    ) -> Result<Option<AccountInfo>, <Db as Database>::Error> {
        self.inner.db_mut().basic(address)
    }

    /// Get the current nonce for a specific address
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn try_read_nonce(&mut self, address: Address) -> Result<u64, <Db as Database>::Error> {
        self.try_read_account(address).map(|a| a.map(|a| a.nonce).unwrap_or_default())
    }

    /// Get the current nonce for a specific address
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn try_read_balance(&mut self, address: Address) -> Result<U256, <Db as Database>::Error> {
        self.try_read_account(address).map(|a| a.map(|a| a.balance).unwrap_or_default())
    }

    /// Get the value of a storage slot.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn try_read_storage(
        &mut self,
        address: Address,
        slot: U256,
    ) -> Result<U256, <Db as Database>::Error> {
        self.inner.db_mut().storage(address, slot)
    }

    /// Get the code at the given account, if any.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn try_read_code(
        &mut self,
        address: Address,
    ) -> Result<Option<Bytecode>, <Db as Database>::Error> {
        let acct_info = self.try_read_account(address)?;
        match acct_info {
            Some(acct) => Ok(Some(self.inner.db_mut().code_by_hash(acct.code_hash)?)),
            None => Ok(None),
        }
    }

    /// Get the gas allowance for a specific caller and gas price.
    pub fn try_gas_allowance(
        &mut self,
        caller: Address,
        gas_price: u128,
    ) -> Result<u64, <Db as Database>::Error> {
        if gas_price == 0 {
            return Ok(u64::MAX);
        }
        let gas_price = U256::from(gas_price);
        let balance = self.try_read_balance(caller)?;
        Ok((balance / gas_price).saturating_to())
    }
}

// Fallible DB Reads with &self
impl<Db, Insp, TrevmState> Trevm<Db, Insp, TrevmState>
where
    Db: Database + DatabaseRef,
    Insp: Inspector<Ctx<Db>>,
{
    /// Get the current account info for a specific address.
    pub fn try_read_account_ref(
        &self,
        address: Address,
    ) -> Result<Option<AccountInfo>, <Db as DatabaseRef>::Error> {
        self.inner.db_ref().basic_ref(address)
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
        self.inner.db_ref().storage_ref(address, slot)
    }

    /// Get the code at the given account, if any.
    pub fn try_read_code_ref(
        &self,
        address: Address,
    ) -> Result<Option<Bytecode>, <Db as DatabaseRef>::Error> {
        let acct_info = self.try_read_account_ref(address)?;
        match acct_info {
            Some(acct) => Ok(Some(self.inner.db_ref().code_by_hash_ref(acct.code_hash)?)),
            None => Ok(None),
        }
    }

    /// Get the gas allowance for a specific caller and gas price.
    pub fn try_gas_allowance_ref(
        &self,
        caller: Address,
        gas_price: U256,
    ) -> Result<u64, <Db as DatabaseRef>::Error> {
        if gas_price.is_zero() {
            return Ok(u64::MAX);
        }
        let gas_price = U256::from(gas_price);
        let balance = self.try_read_balance_ref(caller)?;
        Ok((balance / gas_price).saturating_to())
    }
}

// Infallible DB Reads with &mut self
impl<Db, Insp, TrevmState> Trevm<Db, Insp, TrevmState>
where
    Db: Database<Error = Infallible>,
    Insp: Inspector<Ctx<Db>>,
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

// Infalible DB Reads with &self
impl<Db, Insp, TrevmState> Trevm<Db, Insp, TrevmState>
where
    Db: Database + DatabaseRef,
    Insp: Inspector<Ctx<Db>>,
{
    /// Get the current account info for a specific address.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn read_account_ref(&self, address: Address) -> Option<AccountInfo> {
        self.inner.db_ref().basic_ref(address).expect("infallible")
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
        self.inner.db_ref().storage_ref(address, slot).expect("infallible")
    }

    /// Get the code at the given account, if any.
    ///
    /// Note: due to revm's DB model, this requires a mutable pointer.
    pub fn read_code_ref(&self, address: Address) -> Option<Bytecode> {
        let acct_info = self.read_account_ref(address)?;
        Some(self.inner.db_ref().code_by_hash_ref(acct_info.code_hash).expect("infallible"))
    }
}

impl<Db, Insp, TrevmState> Trevm<Db, Insp, TrevmState>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    /// Commit a set of state changes to the database. This is a low-level API,
    /// and is not intended for general use. Regular users should prefer
    /// executing a transaction.
    pub fn commit_unchecked(&mut self, state: EvmState)
    where
        Db: DatabaseCommit,
    {
        self.inner.db_mut().commit(state);
    }

    /// Modify an account with a closure and commit the modified account. This
    /// is a low-level API, and is not intended for general use.
    pub fn try_modify_account_unchecked<F: FnOnce(&mut AccountInfo)>(
        &mut self,
        address: Address,
        f: F,
    ) -> Result<AccountInfo, <Db as Database>::Error>
    where
        Db: DatabaseCommit,
    {
        self.inner.modify_account(address, f)
    }

    /// Set the nonce of an account, returning the previous nonce. This is a
    /// low-level API, and is not intended for general use.
    pub fn try_set_nonce_unchecked(
        &mut self,
        address: Address,
        nonce: u64,
    ) -> Result<u64, <Db as Database>::Error>
    where
        Db: DatabaseCommit,
    {
        self.inner.set_nonce(address, nonce)
    }

    /// Increment the nonce of an account, returning the previous nonce. This is
    /// a low-level API, and is not intended for general use.
    ///
    /// If the nonce is already at the maximum value, it will not be
    /// incremented.
    pub fn try_increment_nonce_unchecked(
        &mut self,
        address: Address,
    ) -> Result<u64, <Db as Database>::Error>
    where
        Db: DatabaseCommit,
    {
        self.inner.increment_nonce(address)
    }

    /// Decrement the nonce of an account, returning the previous nonce. This is
    /// a low-level API, and is not intended for general use.
    ///
    /// If the nonce is already 0, it will not be decremented.
    pub fn try_decrement_nonce_unchecked(
        &mut self,
        address: Address,
    ) -> Result<u64, <Db as Database>::Error>
    where
        Db: DatabaseCommit,
    {
        self.inner.decrement_nonce(address)
    }

    /// Set the EVM storage at a slot. This is a low-level API, and is not
    /// intended for general use.
    pub fn try_set_storage_unchecked(
        &mut self,
        address: Address,
        slot: U256,
        value: U256,
    ) -> Result<U256, <Db as Database>::Error>
    where
        Db: DatabaseCommit,
    {
        self.inner.set_storage(address, slot, value)
    }

    /// Set the bytecode at a specific address, returning the previous bytecode
    /// at that address. This is a low-level API, and is not intended for
    /// general use.
    pub fn try_set_bytecode_unchecked(
        &mut self,
        address: Address,
        bytecode: Bytecode,
    ) -> Result<Option<Bytecode>, <Db as Database>::Error>
    where
        Db: DatabaseCommit,
    {
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
    ) -> Result<U256, <Db as Database>::Error>
    where
        Db: DatabaseCommit,
    {
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
    ) -> Result<U256, <Db as Database>::Error>
    where
        Db: DatabaseCommit,
    {
        self.inner.decrease_balance(address, amount)
    }

    /// Set the balance of an account. Returns the previous balance. This is a
    /// low-level API, and is not intended for general use.
    pub fn try_set_balance_unchecked(
        &mut self,
        address: Address,
        amount: U256,
    ) -> Result<U256, <Db as Database>::Error>
    where
        Db: DatabaseCommit,
    {
        self.inner.set_balance(address, amount)
    }
}

impl<Db, Insp, TrevmState> Trevm<Db, Insp, TrevmState>
where
    Db: Database<Error = Infallible>,
    Insp: Inspector<Ctx<Db>>,
{
    /// Modify an account with a closure and commit the modified account. This
    /// is a low-level API, and is not intended for general use.
    pub fn modify_account_unchecked(
        &mut self,
        address: Address,
        f: impl FnOnce(&mut AccountInfo),
    ) -> AccountInfo
    where
        Db: DatabaseCommit,
    {
        self.try_modify_account_unchecked(address, f).expect("infallible")
    }

    /// Set the nonce of an account, returning the previous nonce. This is a
    /// low-level API, and is not intended for general use.
    pub fn set_nonce_unchecked(&mut self, address: Address, nonce: u64) -> u64
    where
        Db: DatabaseCommit,
    {
        self.try_set_nonce_unchecked(address, nonce).expect("infallible")
    }

    /// Increment the nonce of an account, returning the previous nonce. This is
    /// a low-level API, and is not intended for general use.
    ///
    /// If this would cause the nonce to overflow, the nonce will be set to the
    /// maximum value.
    pub fn increment_nonce_unchecked(&mut self, address: Address) -> u64
    where
        Db: DatabaseCommit,
    {
        self.try_increment_nonce_unchecked(address).expect("infallible")
    }

    /// Decrement the nonce of an account, returning the previous nonce. This is
    /// a low-level API, and is not intended for general use.
    ///
    /// If this would cause the nonce to underflow, the nonce will be set to 0.
    pub fn decrement_nonce_unchecked(&mut self, address: Address) -> u64
    where
        Db: DatabaseCommit,
    {
        self.try_decrement_nonce_unchecked(address).expect("infallible")
    }

    /// Set the EVM storage at a slot. This is a low-level API, and is not
    /// intended for general use.
    pub fn set_storage_unchecked(&mut self, address: Address, slot: U256, value: U256) -> U256
    where
        Db: DatabaseCommit,
    {
        self.try_set_storage_unchecked(address, slot, value).expect("infallible")
    }

    /// Set the bytecode at a specific address, returning the previous bytecode
    /// at that address. This is a low-level API, and is not intended for
    /// general use.
    pub fn set_bytecode_unchecked(
        &mut self,
        address: Address,
        bytecode: Bytecode,
    ) -> Option<Bytecode>
    where
        Db: DatabaseCommit,
    {
        self.try_set_bytecode_unchecked(address, bytecode).expect("infallible")
    }

    /// Increase the balance of an account. Returns the previous balance. This
    /// is a low-level API, and is not intended for general use.
    pub fn increase_balance_unchecked(&mut self, address: Address, amount: U256) -> U256
    where
        Db: DatabaseCommit,
    {
        self.try_increase_balance_unchecked(address, amount).expect("infallible")
    }

    /// Decrease the balance of an account. Returns the previous balance. This
    /// is a low-level API, and is not intended for general use.
    pub fn decrease_balance_unchecked(&mut self, address: Address, amount: U256) -> U256
    where
        Db: DatabaseCommit,
    {
        self.try_decrease_balance_unchecked(address, amount).expect("infallible")
    }

    /// Set the balance of an account. Returns the previous balance. This is a
    /// low-level API, and is not intended for general use.
    pub fn set_balance_unchecked(&mut self, address: Address, amount: U256) -> U256
    where
        Db: DatabaseCommit,
    {
        self.try_set_balance_unchecked(address, amount).expect("infallible")
    }
}

// Layered inspector
impl<Db, Outer, Inner, TrevmState> Trevm<Db, Layered<Outer, Inner>, TrevmState>
where
    Db: Database,
    Outer: Inspector<Ctx<Db>>,
    Inner: Inspector<Ctx<Db>>,
{
    /// Remove the outer-layer inspector, leaving the inner-layer inspector in
    /// place.
    pub fn take_outer(self) -> (Outer, Trevm<Db, Inner, TrevmState>) {
        let (outer, inner) = self.inner.inspector.into_parts();

        (
            outer,
            Trevm {
                inner: Box::new(Evm {
                    ctx: self.inner.ctx,
                    inspector: inner,
                    instruction: self.inner.instruction,
                    precompiles: self.inner.precompiles,
                    frame_stack: self.inner.frame_stack,
                }),
                state: self.state,
            },
        )
    }

    /// Remove the outer-layer inspector, leaving the inner-layer inspector in
    /// place.
    pub fn remove_outer(self) -> Trevm<Db, Inner, TrevmState> {
        self.take_outer().1
    }

    /// Remove the inner-layer inspector, leaving the outer-layer inspector in
    /// place.
    pub fn take_inner(self) -> (Inner, Trevm<Db, Outer, TrevmState>) {
        let (outer, inner) = self.inner.inspector.into_parts();

        (
            inner,
            Trevm {
                inner: Box::new(Evm {
                    ctx: self.inner.ctx,
                    inspector: outer,
                    instruction: self.inner.instruction,
                    precompiles: self.inner.precompiles,
                    frame_stack: self.inner.frame_stack,
                }),
                state: self.state,
            },
        )
    }

    /// Remove the inner-layer inspector, leaving the outer-layer inspector in
    /// place.
    pub fn remove_inner(self) -> Trevm<Db, Outer, TrevmState> {
        self.take_inner().1
    }
}

// --- ALL STATES, WITH State<Db>

impl<Db, Insp, TrevmState> Trevm<Db, Insp, TrevmState>
where
    Db: Database + StateAcc,
    Insp: Inspector<Ctx<Db>>,
{
    /// Set the [EIP-161] state clear flag, activated in the Spurious Dragon
    /// hardfork.
    pub fn set_state_clear_flag(&mut self, flag: bool) {
        self.inner.db_mut().set_state_clear_flag(flag)
    }
}

impl<Db, Insp, TrevmState> Trevm<Db, Insp, TrevmState>
where
    Db: Database + TryStateAcc,
    Insp: Inspector<Ctx<Db>>,
{
    /// Fallibly set the [EIP-161] state clear flag, activated in the Spurious
    /// Dragon hardfork. This function is intended to be used by shared states,
    /// where mutable access may fail, e.g. an `Arc<Db>`.
    ///
    /// Prefer [`Self::set_state_clear_flag`] when available.
    pub fn try_set_state_clear_flag(
        &mut self,
        flag: bool,
    ) -> Result<(), <Db as TryStateAcc>::Error> {
        self.inner.db_mut().try_set_state_clear_flag(flag)
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
