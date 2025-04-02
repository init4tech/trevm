use revm::{
    inspector::NoOpInspector,
    interpreter::{
        CallInputs, CallOutcome, CreateInputs, CreateOutcome, EOFCreateInputs, Interpreter,
        InterpreterTypes,
    },
    primitives::{Address, Log, U256},
    Inspector,
};

/// A layer in a stack of inspectors. Contains its own inspector and an
/// inner inspector. This is used to create a stack of inspectors that can
/// be used to inspect the execution of a contract.
///
/// The current inspector will be invoked first, then the inner inspector.
/// For functions that may return values (e.g. [`Inspector::call`]), if the
/// current inspector returns a value, the inner inspector will not be invoked.
#[derive(Clone, Debug)]
pub struct Layered<Outer, Inner = NoOpInspector> {
    current: Outer,
    inner: Inner,
}

impl<Ctx, Int: InterpreterTypes, Outer, Inner> Inspector<Ctx, Int> for Layered<Outer, Inner>
where
    Outer: Inspector<Ctx, Int>,
    Inner: Inspector<Ctx, Int>,
{
    fn initialize_interp(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx) {
        self.current.initialize_interp(interp, context);
        self.inner.initialize_interp(interp, context);
    }

    fn step(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx) {
        self.current.step(interp, context);
        self.inner.step(interp, context);
    }

    fn step_end(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx) {
        self.current.step_end(interp, context);
        self.inner.step_end(interp, context);
    }

    fn log(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx, log: Log) {
        self.current.log(interp, context, log.clone());
        self.inner.log(interp, context, log);
    }

    fn call(&mut self, context: &mut Ctx, inputs: &mut CallInputs) -> Option<CallOutcome> {
        if let Some(outcome) = self.current.call(context, inputs) {
            return Some(outcome);
        }
        self.inner.call(context, inputs)
    }

    fn call_end(&mut self, context: &mut Ctx, inputs: &CallInputs, outcome: &mut CallOutcome) {
        self.current.call_end(context, inputs, outcome);
        self.inner.call_end(context, inputs, outcome);
    }

    fn create(&mut self, context: &mut Ctx, inputs: &mut CreateInputs) -> Option<CreateOutcome> {
        if let Some(outcome) = self.current.create(context, inputs) {
            return Some(outcome);
        }
        self.inner.create(context, inputs)
    }

    fn create_end(
        &mut self,
        context: &mut Ctx,
        inputs: &CreateInputs,
        outcome: &mut CreateOutcome,
    ) {
        self.current.create_end(context, inputs, outcome);
        self.inner.create_end(context, inputs, outcome);
    }

    fn eofcreate(
        &mut self,
        context: &mut Ctx,
        inputs: &mut EOFCreateInputs,
    ) -> Option<CreateOutcome> {
        if let Some(outcome) = self.current.eofcreate(context, inputs) {
            return Some(outcome);
        }
        self.inner.eofcreate(context, inputs)
    }

    fn eofcreate_end(
        &mut self,
        context: &mut Ctx,
        inputs: &EOFCreateInputs,
        outcome: &mut CreateOutcome,
    ) {
        self.current.eofcreate_end(context, inputs, outcome);
        self.inner.eofcreate_end(context, inputs, outcome);
    }

    fn selfdestruct(&mut self, contract: Address, target: Address, value: U256) {
        self.current.selfdestruct(contract, target, value);
        self.inner.selfdestruct(contract, target, value);
    }
}
