use crate::{EvmNeedsCfg, Trevm, TrevmBuilder};
use alloy_primitives::{Address, U256};
use revm::{
    db::{CacheDB, EmptyDB, InMemoryDB, State},
    inspector_handle_register,
    primitives::{AccountInfo, Bytecode},
    EvmBuilder, GetInspector,
};

use revm::inspectors::TracerEip3155;

pub use revm::test_utils as revm_test_utils;

impl<Ext, State> Trevm<'_, Ext, InMemoryDB, State> {
    /// Modify an account with the provide closure. Returns the original
    /// account info
    pub fn test_modify_account<F>(&mut self, address: Address, f: F) -> AccountInfo
    where
        F: FnOnce(&mut AccountInfo),
    {
        self.modify_account_unchecked(address, f)
    }

    /// Set the nonce of an account, returning the previous nonce.
    pub fn test_set_nonce(&mut self, address: Address, nonce: u64) -> u64 {
        self.set_nonce_unchecked(address, nonce)
    }

    /// Increment the nonce of an account, returning the previous nonce.
    ///
    /// If this would cause the nonce to overflow, the nonce will be set to the
    /// maximum value.
    pub fn test_increment_nonce(&mut self, address: Address) -> u64 {
        self.increment_nonce_unchecked(address)
    }

    /// Decrement the nonce of an account, returning the previous nonce.
    ///
    /// If this would cause the nonce to underflow, the nonce will be set to
    /// 0.
    pub fn test_decrement_nonce(&mut self, address: Address) -> u64 {
        self.decrement_nonce_unchecked(address)
    }

    /// Set the EVM storage at a slot.
    pub fn test_set_storage(&mut self, address: Address, slot: U256, value: U256) -> U256 {
        self.set_storage_unchecked(address, slot, value)
    }

    /// Set the bytecode at a specific address, returning the previous bytecode
    /// at that address.
    pub fn test_set_bytecode(&mut self, address: Address, bytecode: Bytecode) -> Option<Bytecode> {
        self.set_bytecode_unchecked(address, bytecode)
    }

    /// Increase the balance of an account. Returns the previous balance.
    ///
    /// If this would cause the balance to overflow, the balance will be set
    /// to `U256::MAX`.
    pub fn test_increase_balance(&mut self, address: Address, amount: U256) -> U256 {
        self.increase_balance_unchecked(address, amount)
    }

    /// Decrease the balance of an account. Returns the previous balance.
    ///
    /// If this would cause the balance to underflow, the balance will be set
    /// to `U256::ZERO`.
    pub fn test_decrease_balance(&mut self, address: Address, amount: U256) -> U256 {
        self.decrease_balance_unchecked(address, amount)
    }

    /// Set the balance of an account. Returns the previous balance.
    pub fn test_set_balance(&mut self, address: Address, amount: U256) -> U256 {
        self.set_balance_unchecked(address, amount)
    }
}

/// Make a new [`Trevm`] with the given inspector and an in-memory database.
pub fn test_trevm_with_inspector<I>(inspector: I) -> EvmNeedsCfg<'static, I, CacheDB<EmptyDB>>
where
    I: GetInspector<InMemoryDB>,
{
    EvmBuilder::default()
        .with_db(CacheDB::new(EmptyDB::default()))
        .with_external_context(inspector)
        .append_handler_register(inspector_handle_register)
        .build_trevm()
}

/// Make a new [`Trevm`], funding the provided accounts with the given
/// amounts.
pub fn test_trevm_with_funds<'b, I>(i: I) -> EvmNeedsCfg<'static, (), InMemoryDB>
where
    I: IntoIterator<Item = &'b (Address, U256)>,
{
    let mut trevm = test_trevm();

    for (address, amount) in i {
        trevm.test_set_balance(*address, *amount);
    }

    trevm
}

/// Make a new [`Trevm`] with an in-memory database.
pub fn test_trevm() -> EvmNeedsCfg<'static, (), CacheDB<EmptyDB>> {
    EvmBuilder::default().with_db(CacheDB::new(EmptyDB::default())).build_trevm()
}

/// Make a new [`Trevm`] with an in-memory database wrapped in a [`State`].
pub fn test_state_trevm() -> EvmNeedsCfg<'static, (), State<EmptyDB>> {
    EvmBuilder::default().with_db(State::builder().with_bundle_update().build()).build_trevm()
}

/// Make a new [`Trevm`] with an in-memory database and a tracer inspector.
/// The tracer will print all EVM instructions to stdout.
pub fn test_trevm_tracing() -> EvmNeedsCfg<'static, TracerEip3155, CacheDB<EmptyDB>> {
    test_trevm_with_inspector(TracerEip3155::new(Box::new(std::io::stdout())))
}
