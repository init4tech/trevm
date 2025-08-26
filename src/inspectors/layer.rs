use revm::{
    interpreter::{
        CallInputs, CallOutcome, CreateInputs, CreateOutcome, Interpreter, InterpreterTypes,
    },
    primitives::{Address, Log, U256},
    Inspector,
};

/// A layer in a stack of inspectors. Contains its own inspector and an
/// inner inspector. This is used to create a stack of inspectors that can
/// be used to inspect the execution of a contract.
///
/// Use `Layered` when you need to retain type information about the inner
/// inspectors.
///
/// The current inspector will be invoked first, then the inner inspector.
/// For functions that may return values (e.g. [`Inspector::call`]), if the
/// current inspector returns a value, the inner inspector will not be invoked.
#[derive(Clone, Debug)]
pub struct Layered<Outer, Inner> {
    outer: Outer,
    inner: Inner,
}

impl<Outer, Inner> Layered<Outer, Inner> {
    /// Create a new [`Layered`] inspector with the given current and inner
    /// inspectors.
    pub const fn new(outer: Outer, inner: Inner) -> Self {
        Self { outer, inner }
    }

    /// Wrap this inspector in another, creating a new [`Layered`] inspector.
    /// with this as the inner inspector.
    pub const fn wrap_in<Other>(self, outer: Other) -> Layered<Other, Self> {
        Layered { outer, inner: self }
    }

    /// Wrap this inspector around another, creating a new [`Layered`] inspector
    /// with this as the outer inspector.
    pub const fn wrap_around<Other>(self, inner: Other) -> Layered<Self, Other> {
        Layered { outer: self, inner }
    }

    /// Decompose the [`Layered`] inspector into its outer and inner
    /// inspectors.
    pub fn into_parts(self) -> (Outer, Inner) {
        (self.outer, self.inner)
    }

    /// Get a reference to the outer inspector.
    pub const fn outer(&self) -> &Outer {
        &self.outer
    }

    /// Get a mutable reference to the outer inspector.
    pub const fn outer_mut(&mut self) -> &mut Outer {
        &mut self.outer
    }

    /// Get a reference to the inner inspector.
    pub const fn inner(&self) -> &Inner {
        &self.inner
    }

    /// Get a mutable reference to the inner inspector.
    pub const fn inner_mut(&mut self) -> &mut Inner {
        &mut self.inner
    }
}

impl<Ctx, Int: InterpreterTypes, Outer, Inner> Inspector<Ctx, Int> for Layered<Outer, Inner>
where
    Outer: Inspector<Ctx, Int>,
    Inner: Inspector<Ctx, Int>,
{
    fn initialize_interp(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx) {
        self.outer.initialize_interp(interp, context);
        self.inner.initialize_interp(interp, context);
    }

    fn step(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx) {
        self.outer.step(interp, context);
        self.inner.step(interp, context);
    }

    fn step_end(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx) {
        self.outer.step_end(interp, context);
        self.inner.step_end(interp, context);
    }

    fn log(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx, log: Log) {
        self.outer.log(interp, context, log.clone());
        self.inner.log(interp, context, log);
    }

    fn call(&mut self, context: &mut Ctx, inputs: &mut CallInputs) -> Option<CallOutcome> {
        if let Some(outcome) = self.outer.call(context, inputs) {
            return Some(outcome);
        }
        self.inner.call(context, inputs)
    }

    fn call_end(&mut self, context: &mut Ctx, inputs: &CallInputs, outcome: &mut CallOutcome) {
        self.outer.call_end(context, inputs, outcome);
        self.inner.call_end(context, inputs, outcome);
    }

    fn create(&mut self, context: &mut Ctx, inputs: &mut CreateInputs) -> Option<CreateOutcome> {
        if let Some(outcome) = self.outer.create(context, inputs) {
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
        self.outer.create_end(context, inputs, outcome);
        self.inner.create_end(context, inputs, outcome);
    }

    fn selfdestruct(&mut self, contract: Address, target: Address, value: U256) {
        self.outer.selfdestruct(contract, target, value);
        self.inner.selfdestruct(contract, target, value);
    }
}
