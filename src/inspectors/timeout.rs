use crate::helpers::Ctx;
use revm::{
    context_interface::context::ContextError,
    interpreter::{
        CallInputs, CallOutcome, CreateInputs, CreateOutcome, EOFCreateInputs, Interpreter,
        InterpreterTypes,
    },
    Database, Inspector,
};
use std::time::{Duration, Instant};

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
/// [`ContextError::Custom`], which will be propagated as an
/// [`EVMError::Custom`] to the caller of the EVM interpreter.
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
///
/// [EIP-150]: https://eips.ethereum.org/EIPS/eip-150
/// [`EVMError::Custom`]: revm::context::result::EVMError::Custom
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
        let elapsed = self.execution_start.elapsed();
        println!("elapsed: {elapsed:?}, duration: {}ms", self.duration.as_millis());
        elapsed >= self.duration
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

macro_rules! check_timeout {
    ($self:ident, $ctx:ident) => {
        if $self.has_elapsed() {
            $ctx.error = Err(ContextError::Custom("timeout during evm execution".to_string()));
        }
    };
}

impl<Db: Database, Int: InterpreterTypes> Inspector<Ctx<Db>, Int> for TimeLimit {
    fn initialize_interp(&mut self, _interp: &mut Interpreter<Int>, _ctx: &mut Ctx<Db>) {
        self.reset();
    }

    fn call(&mut self, ctx: &mut Ctx<Db>, _inputs: &mut CallInputs) -> Option<CallOutcome> {
        println!("call");
        check_timeout!(self, ctx);

        None
    }

    fn call_end(&mut self, ctx: &mut Ctx<Db>, _inputs: &CallInputs, _outcome: &mut CallOutcome) {
        println!("call_end");
        check_timeout!(self, ctx);
    }

    fn create(&mut self, ctx: &mut Ctx<Db>, _inputs: &mut CreateInputs) -> Option<CreateOutcome> {
        println!("create");
        check_timeout!(self, ctx);

        None
    }

    fn create_end(
        &mut self,
        ctx: &mut Ctx<Db>,
        _inputs: &CreateInputs,
        _outcome: &mut CreateOutcome,
    ) {
        println!("create_end");
        check_timeout!(self, ctx);
    }

    fn eofcreate(
        &mut self,
        ctx: &mut Ctx<Db>,
        _inputs: &mut EOFCreateInputs,
    ) -> Option<CreateOutcome> {
        println!("eofcreate");
        check_timeout!(self, ctx);

        None
    }

    fn eofcreate_end(
        &mut self,
        ctx: &mut Ctx<Db>,
        _inputs: &EOFCreateInputs,
        _outcome: &mut CreateOutcome,
    ) {
        println!("eofcreate_end");
        check_timeout!(self, ctx);
    }
}
