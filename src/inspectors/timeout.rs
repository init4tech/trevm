use revm::{
    interpreter::{
        CallInputs, CallOutcome, CreateInputs, CreateOutcome, EOFCreateInputs, Gas,
        InstructionResult, Interpreter, InterpreterResult, InterpreterTypes,
    },
    primitives::Bytes,
    Inspector,
};
use std::time::{Duration, Instant};

const CALL_TIMEOUT: CallOutcome = CallOutcome {
    result: InterpreterResult {
        result: InstructionResult::CallTooDeep,
        output: Bytes::new(),
        gas: Gas::new_spent(0),
    },
    memory_offset: 0..0,
};

const CREATE_TIMEOUT: CreateOutcome = CreateOutcome {
    result: InterpreterResult {
        result: InstructionResult::CallTooDeep,
        output: Bytes::new(),
        gas: Gas::new_spent(0),
    },
    address: None,
};

/// A revm [`Inspector`] that limits wallclock time spent on execution.
///
/// This inspector will stop execution at the beginning and end of each
/// callframe after the timeout has been reached. Specifically, it will stop
/// when:
/// - any callframe is aborted (e.g. due to execeeding its gas limit)
/// - any of the following instructions are executed:
///     - `CALL`
///     - `CREATE`
///     - `RETURN`
///     - `STOP`
///     - `REVERT`
///     - any invalid opcode
///
/// When execution is terminated by the timer, it will result in a
/// [`InstructionResult::CallTooDeep`].
///
/// ## Usage Note
///
/// When the timeout is triggered, the inspector will overwrite the
/// [`CallOutcome`] or [`CreateOutcome`]. This means that if other inspectors
/// have already run, they may have inspected data that is no longer valid.
///
/// To avoid this, run this inspector FIRST on any multi-inspector setup. I.e.
/// in a stack, this should be the OUTERMOST inspector. This ensures that
/// invalid data is not inspected, and that other inspectors do not consume
/// memory or compute resources inspecting data that is guaranteed to be
/// discarded.
#[derive(Debug, Clone, Copy)]
pub struct TimeLimit {
    duration: Duration,
    execution_start: Instant,
}

impl TimeLimit {
    /// Create a new [`TimeLimit`] inspector.
    ///
    /// The inspector will stop execution after the given duration has passed.
    pub fn new(duration: Duration) -> Self {
        Self { duration, execution_start: Instant::now() }
    }

    /// Check if the timeout has been reached.
    pub fn has_elapsed(&self) -> bool {
        self.execution_start.elapsed() >= self.duration
    }

    /// Set the execution start time to [`Instant::now`]. This is invoked during [`Inspector::initialize_interp`].
    pub fn reset(&mut self) {
        self.execution_start = Instant::now();
    }

    /// Get the amount of time that has elapsed since execution start.
    pub fn elapsed(&self) -> Duration {
        self.execution_start.elapsed()
    }
}

impl<Ctx, Int: InterpreterTypes> Inspector<Ctx, Int> for TimeLimit {
    fn initialize_interp(&mut self, _interp: &mut Interpreter<Int>, _context: &mut Ctx) {
        self.reset();
    }

    fn call(&mut self, _context: &mut Ctx, _inputs: &mut CallInputs) -> Option<CallOutcome> {
        if self.has_elapsed() {
            return Some(CALL_TIMEOUT);
        }

        None
    }

    fn call_end(&mut self, _context: &mut Ctx, _inputs: &CallInputs, outcome: &mut CallOutcome) {
        if self.has_elapsed() {
            *outcome = CALL_TIMEOUT;
        }
    }

    fn create(&mut self, _context: &mut Ctx, _inputs: &mut CreateInputs) -> Option<CreateOutcome> {
        if self.has_elapsed() {
            return Some(CREATE_TIMEOUT);
        }
        None
    }

    fn create_end(
        &mut self,
        _context: &mut Ctx,
        _inputs: &CreateInputs,
        outcome: &mut CreateOutcome,
    ) {
        if self.has_elapsed() {
            *outcome = CREATE_TIMEOUT;
        }
    }

    fn eofcreate(
        &mut self,
        _context: &mut Ctx,
        _inputs: &mut EOFCreateInputs,
    ) -> Option<CreateOutcome> {
        if self.has_elapsed() {
            return Some(CREATE_TIMEOUT);
        }

        None
    }

    fn eofcreate_end(
        &mut self,
        _context: &mut Ctx,
        _inputs: &EOFCreateInputs,
        outcome: &mut CreateOutcome,
    ) {
        if self.has_elapsed() {
            *outcome = CREATE_TIMEOUT;
        }
    }
}
