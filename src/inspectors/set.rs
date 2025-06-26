use std::collections::VecDeque;

use revm::{
    interpreter::{
        CallInputs, CallOutcome, CreateInputs, CreateOutcome, Interpreter,
        InterpreterTypes,
    },
    primitives::{Address, Log, U256},
    Inspector,
};

/// A stack of [`Inspector`]s.
///
/// This is a thin wrapper around a [`VecDeque`] of inspectors.
#[derive(Default)]
pub struct InspectorSet<Ctx, Int> {
    inspectors: VecDeque<Box<dyn Inspector<Ctx, Int>>>,
}

impl<Ctx, Int> core::ops::Deref for InspectorSet<Ctx, Int> {
    type Target = VecDeque<Box<dyn Inspector<Ctx, Int>>>;

    fn deref(&self) -> &Self::Target {
        &self.inspectors
    }
}

impl<Ctx, Int> core::ops::DerefMut for InspectorSet<Ctx, Int> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inspectors
    }
}

impl<Ctx, Int> core::fmt::Debug for InspectorSet<Ctx, Int> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InspectorStack").field("inspectors", &self.inspectors.len()).finish()
    }
}

impl<Ctx, Int> InspectorSet<Ctx, Int>
where
    Int: InterpreterTypes,
{
    /// Instantiate a new empty inspector stack.
    pub fn new() -> Self {
        Self { inspectors: Default::default() }
    }

    /// Instantiate a new empty stack with pre-allocated capacity.
    pub fn with_capacity(cap: usize) -> Self {
        Self { inspectors: VecDeque::with_capacity(cap) }
    }

    /// Push an inspector to the back of the stack.
    pub fn push_back<I: Inspector<Ctx, Int> + 'static>(&mut self, inspector: I) {
        self.inspectors.push_back(Box::new(inspector));
    }

    /// Push an inspector to the front of the stack.
    pub fn push_front<I: Inspector<Ctx, Int> + 'static>(&mut self, inspector: I) {
        self.inspectors.push_front(Box::new(inspector));
    }

    /// Pop an inspector from the back of the stack.
    pub fn pop_back(&mut self) -> Option<Box<dyn Inspector<Ctx, Int>>> {
        self.inspectors.pop_back()
    }

    /// Pop an inspector from the front of the stack.
    pub fn pop_front(&mut self) -> Option<Box<dyn Inspector<Ctx, Int>>> {
        self.inspectors.pop_front()
    }
}

impl<Ctx, Int> Inspector<Ctx, Int> for InspectorSet<Ctx, Int>
where
    Int: InterpreterTypes,
{
    fn initialize_interp(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx) {
        self.inspectors.iter_mut().for_each(|i| i.initialize_interp(interp, context));
    }

    fn step(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx) {
        self.inspectors.iter_mut().for_each(|i| i.step(interp, context));
    }

    fn step_end(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx) {
        self.inspectors.iter_mut().for_each(|i| i.step_end(interp, context));
    }

    fn log(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx, log: Log) {
        self.inspectors.iter_mut().for_each(|i| i.log(interp, context, log.clone()));
    }

    fn call(&mut self, context: &mut Ctx, inputs: &mut CallInputs) -> Option<CallOutcome> {
        for inspector in self.inspectors.iter_mut() {
            let outcome = inspector.call(context, inputs);
            if outcome.is_some() {
                return outcome;
            }
        }
        None
    }

    fn call_end(&mut self, context: &mut Ctx, inputs: &CallInputs, outcome: &mut CallOutcome) {
        self.inspectors.iter_mut().for_each(|i| i.call_end(context, inputs, outcome))
    }

    fn create(&mut self, context: &mut Ctx, inputs: &mut CreateInputs) -> Option<CreateOutcome> {
        for inspector in self.inspectors.iter_mut() {
            let outcome = inspector.create(context, inputs);
            if outcome.is_some() {
                return outcome;
            }
        }
        None
    }

    fn create_end(
        &mut self,
        context: &mut Ctx,
        inputs: &CreateInputs,
        outcome: &mut CreateOutcome,
    ) {
        self.inspectors.iter_mut().for_each(|i| i.create_end(context, inputs, outcome))
    }

    fn selfdestruct(&mut self, contract: Address, target: Address, value: U256) {
        self.inspectors.iter_mut().for_each(|i| i.selfdestruct(contract, target, value))
    }
}
