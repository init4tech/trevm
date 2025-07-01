use revm::{
    context::{BlockEnv, CfgEnv, TxEnv},
    context_interface::context::ContextError,
    handler::{instructions::EthInstructions, EthFrame, EthPrecompiles},
    inspector::NoOpInspector,
    interpreter::{interpreter::EthInterpreter, InstructionContext, InterpreterTypes},
    Context, Database, Journal,
};

/// [`revm::Context`] with default env types and adjustable DB
pub type Ctx<Db, J = Journal<Db>, C = ()> = Context<BlockEnv, TxEnv, CfgEnv, Db, J, C>;

/// EVM with default env types and adjustable DB.
pub type Evm<Db, Insp = NoOpInspector, Inst = Instructions<Db>, Prec = EthPrecompiles> =
    revm::context::Evm<Ctx<Db>, Insp, Inst, Prec, EthFrame>;

/// Handler table for EVM opcodes.
pub type Instructions<Db> = EthInstructions<EthInterpreter, Ctx<Db>>;

/// The handler type for an EVM opcode.
pub type Instruction<Db> = revm::interpreter::Instruction<EthInterpreter, Ctx<Db>>;

/// An [`Instruction`] that sets a [`ContextError`] in the [`Ctx`] whenever it
/// is executed.
pub fn forbidden<Db: Database, Int: InterpreterTypes>(ctx: InstructionContext<'_, Ctx<Db>, Int>) {
    ctx.host.error = Err(ContextError::Custom("forbidden opcode".to_string()));
}
