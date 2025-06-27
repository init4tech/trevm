use crate::{helpers::Ctx, EvmNeedsCfg, Trevm};
use alloy::primitives::{Address, U256};
use revm::{
    bytecode::Bytecode,
    database::{CacheDB, EmptyDB, InMemoryDB, State},
    inspector::{inspectors::TracerEip3155, NoOpInspector},
    interpreter::{
        CallInputs, CallOutcome, CreateInputs, CreateOutcome, Interpreter, InterpreterTypes,
    },
    primitives::{hardfork::SpecId, Log},
    state::AccountInfo,
    Context, Inspector, MainBuilder,
};

impl<Insp, State> Trevm<InMemoryDB, Insp, State>
where
    Insp: Inspector<Ctx<InMemoryDB>>,
{
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

/// Make a new [`Trevm`], funding the provided accounts with the given
/// amounts.
pub fn test_trevm_with_funds<'b, I>(i: I) -> EvmNeedsCfg<InMemoryDB, NoOpInspector>
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
pub fn test_trevm() -> EvmNeedsCfg<InMemoryDB, NoOpInspector> {
    Trevm::from(
        Context::new(CacheDB::new(EmptyDB::default()), SpecId::PRAGUE)
            .build_mainnet_with_inspector(NoOpInspector),
    )
}

/// Make a new [`Trevm`] with an in-memory database wrapped in a [`State`].
pub fn test_state_trevm() -> EvmNeedsCfg<State<EmptyDB>, NoOpInspector> {
    Trevm::from(
        Context::new(State::builder().with_bundle_update().build(), SpecId::PRAGUE)
            .build_mainnet_with_inspector(NoOpInspector),
    )
}

/// Make a new [`Trevm`] with an in-memory database and a tracer inspector.
/// The tracer will print all EVM instructions to stdout.
pub fn test_trevm_tracing() -> EvmNeedsCfg<InMemoryDB, TracerEip3155> {
    Trevm::from(
        Context::new(CacheDB::new(EmptyDB::default()), SpecId::PRAGUE)
            .build_mainnet_with_inspector(TracerEip3155::new(Box::new(std::io::stdout()))),
    )
}

/// Inspector that tracks whether the various inspector methods were
/// called. This is useful for testing the inspector stack.
///
/// It is not a real inspector, and does not do anything with the
/// information it collects.
#[derive(Default, Debug, Clone, Copy)]
pub struct TestInspector {
    /// Whether initialize_interp was called.
    pub init_interp: bool,
    /// Whether step was called.
    pub step: bool,
    /// Whether step_end was called.
    pub step_end: bool,
    /// Whether log was called.
    pub log: bool,
    /// Whether call was called.
    pub call: bool,
    /// Whether call_end was called.
    pub call_end: bool,
    /// Whether create was called.
    pub create: bool,
    /// Whether create_end was called.
    pub create_end: bool,
    /// Whether eofcreate was called.
    pub eofcreate: bool,
    /// Whether eofcreate_end was called.
    pub eofcreate_end: bool,
    /// Whether selfdestruct was called.
    pub selfdestruct: bool,
}

impl TestInspector {
    /// Reset the inspector to its default state.
    pub fn reset(&mut self) {
        *self = Self::default();
    }
}

impl<Ctx, Int> Inspector<Ctx, Int> for TestInspector
where
    Int: InterpreterTypes,
{
    fn initialize_interp(&mut self, _interp: &mut Interpreter<Int>, _context: &mut Ctx) {
        tracing::info!("initialize_interp");
        self.init_interp = true;
    }

    fn step(&mut self, _interp: &mut Interpreter<Int>, _context: &mut Ctx) {
        tracing::info!("step");
        self.step = true;
    }

    fn step_end(&mut self, _interp: &mut Interpreter<Int>, _context: &mut Ctx) {
        tracing::info!("step_end");
        self.step_end = true;
    }

    fn log(&mut self, _interp: &mut Interpreter<Int>, _context: &mut Ctx, log: Log) {
        tracing::info!(?log, "log");
        self.log = true;
    }

    fn call(&mut self, _context: &mut Ctx, inputs: &mut CallInputs) -> Option<CallOutcome> {
        tracing::info!(?inputs, "call");
        self.call = true;
        None
    }

    fn call_end(&mut self, _context: &mut Ctx, inputs: &CallInputs, outcome: &mut CallOutcome) {
        tracing::info!(?inputs, ?outcome, "call_end");
        self.call_end = true;
    }

    fn create(&mut self, _context: &mut Ctx, inputs: &mut CreateInputs) -> Option<CreateOutcome> {
        tracing::info!(?inputs, "create");
        self.create = true;
        None
    }

    fn create_end(
        &mut self,
        _context: &mut Ctx,
        _inputs: &CreateInputs,
        _outcome: &mut CreateOutcome,
    ) {
        tracing::info!("create_end");
        self.create_end = true;
    }

    fn selfdestruct(&mut self, contract: Address, target: Address, value: U256) {
        tracing::info!(?contract, ?target, ?value, "selfdestruct");
        self.selfdestruct = true;
    }
}
