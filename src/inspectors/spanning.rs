use alloy::hex;
use revm::{
    interpreter::{
        CallInputs, CallOutcome, CreateInputs, CreateOutcome, EOFCreateInputs, Interpreter,
        InterpreterTypes,
    },
    Inspector,
};
use tracing::{
    debug_span, error_span, info_span, span::EnteredSpan, trace_span, warn_span, Level, Span,
};

macro_rules! runtime_level_span {
    ($level:expr, $($args:tt)*) => {{
        match $level {
            Level::TRACE => trace_span!($($args)*),
            Level::DEBUG => debug_span!($($args)*),
            Level::INFO => info_span!($($args)*),
            Level::WARN => warn_span!($($args)*),
            Level::ERROR => error_span!($($args)*),
        }
    }};
}

/// Inspector that creates spans for each call and create operation.
///
/// This inspector is useful for tracing the execution of the EVM and
/// contextualizing information from other tracing inspectors. It uses
/// [`tracing`] to create spans for each call frame, at a specfied [`Level`],
/// and adds interpreter information to the span.
///
/// Spans are created at the beginning of each call and create operation,
/// and closed at the end of the operation. The spans are named
/// according to the operation type (call or create) and include
/// the call depth, gas remaining, and other relevant information.
///
/// # Note on functionality
///
/// We assume that the EVM execution is synchronous, so [`EnteredSpan`]s will
/// not be held across await points. This means we can simply keep a
/// `Vec<EnteredSpan>` to which push and from which we pop. The first span in
/// the vec will always be our root span, and 1 span will be held for each
/// active callframe.
///
pub struct SpanningInspector {
    active: Vec<EnteredSpan>,
    level: Level,
}

impl core::fmt::Debug for SpanningInspector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SpanningInspector")
            .field("active", &self.active.len())
            .field("level", &self.level)
            .finish()
    }
}

impl SpanningInspector {
    /// Create a new `SpanningInspector` with the given tracing level.
    /// Spans will be created at this level.
    pub const fn new(level: Level) -> Self {
        Self { active: Vec::new(), level }
    }

    /// Create a root span
    fn root_span<Ctx, Int>(&mut self, _interp: &mut Interpreter<Int>, _context: &mut Ctx) -> Span
    where
        Int: InterpreterTypes,
    {
        runtime_level_span!(
            self.level,
            parent: None, // this is the root span :)
            "evm_execution",
        )
    }

    /// Init the inspector by setting the root span. This should be called only in [`Inspector::initialize_interp`].
    fn init<Ctx, Int>(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx)
    where
        Int: InterpreterTypes,
    {
        // just in case
        self.active.clear();
        let span = self.root_span(interp, context).entered();
        self.active.push(span);
    }

    /// Exit the active span.
    fn exit_span(&mut self) {
        self.active.pop();
        // If there's only 1 left, it's the root span for the trace, and all
        // callframes are closed. We are now done with execution.
        if self.active.len() == 1 {
            self.active.pop();
        }
    }

    /// Create a span for a `CALL`-family opcode.
    fn span_call<Ctx>(&self, _context: &Ctx, inputs: &CallInputs) -> Span {
        let mut selector = inputs.input.clone();
        selector.truncate(4);
        runtime_level_span!(
            self.level,
            "call",
            input_len = inputs.input.len(),
            selector = hex::encode(&selector),
            gas_limit = inputs.gas_limit,
            bytecode_address = %inputs.bytecode_address,
            target_addrses = %inputs.target_address,
            caller = %inputs.caller,
            value = %inputs.value.get(),
            scheme = ?inputs.scheme,
        )
    }

    /// Create, enter, and store a span for a `CALL`-family opcode.
    fn enter_call<Ctx>(&mut self, context: &Ctx, inputs: &CallInputs) {
        self.active.push(self.span_call(context, inputs).entered())
    }

    /// Create a span for a `CREATE`-family opcode.
    fn span_create<Ctx>(&self, _context: &Ctx, inputs: &CreateInputs) -> Span {
        runtime_level_span!(
            self.level,
            "create",
            caller = %inputs.caller,
            value = %inputs.value,
            gas_limit = inputs.gas_limit,
            scheme = ?inputs.scheme,
        )
    }

    /// Create, enter, and store a span for a `CREATE`-family opcode.
    fn enter_create<Ctx>(&mut self, context: &Ctx, inputs: &CreateInputs) {
        self.active.push(self.span_create(context, inputs).entered())
    }

    /// Create a span for an EOF `CREATE`-family opcode.
    fn span_eof_create<Ctx>(&self, _context: &Ctx, inputs: &EOFCreateInputs) -> Span {
        runtime_level_span!(
            self.level,
            "eof_create",
            caller = %inputs.caller,
            value = %inputs.value,
            gas_limit = inputs.gas_limit,
            kind = ?inputs.kind,
        )
    }

    /// Create, enter, and store a span for an EOF `CREATE`-family opcode.
    fn enter_eof_create<Ctx>(&mut self, context: &Ctx, inputs: &EOFCreateInputs) {
        self.active.push(self.span_eof_create(context, inputs).entered())
    }
}

impl<Ctx, Int> Inspector<Ctx, Int> for SpanningInspector
where
    Int: InterpreterTypes,
{
    fn initialize_interp(&mut self, interp: &mut Interpreter<Int>, context: &mut Ctx) {
        self.init(interp, context);
    }

    fn call(&mut self, context: &mut Ctx, inputs: &mut CallInputs) -> Option<CallOutcome> {
        self.enter_call(context, inputs);
        None
    }

    fn call_end(&mut self, _context: &mut Ctx, _inputs: &CallInputs, _outcome: &mut CallOutcome) {
        self.exit_span();
    }

    fn create(&mut self, context: &mut Ctx, inputs: &mut CreateInputs) -> Option<CreateOutcome> {
        self.enter_create(context, inputs);
        None
    }

    fn create_end(
        &mut self,
        _context: &mut Ctx,
        _inputs: &CreateInputs,
        _outcome: &mut CreateOutcome,
    ) {
        self.exit_span();
    }

    fn eofcreate(
        &mut self,
        context: &mut Ctx,
        inputs: &mut EOFCreateInputs,
    ) -> Option<CreateOutcome> {
        self.enter_eof_create(context, inputs);
        None
    }

    fn eofcreate_end(
        &mut self,
        _context: &mut Ctx,
        _inputs: &EOFCreateInputs,
        _outcome: &mut CreateOutcome,
    ) {
        self.exit_span();
    }
}
