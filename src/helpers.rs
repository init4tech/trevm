use revm::{
    context::{BlockEnv, CfgEnv, TxEnv},
    handler::{instructions::EthInstructions, EthPrecompiles},
    inspector::NoOpInspector,
    interpreter::interpreter::EthInterpreter,
    Context, Journal,
};

/// [`revm::Context`] with default env types and adjustable DB
pub type Ctx<Db, J = Journal<Db>, C = ()> = Context<BlockEnv, TxEnv, CfgEnv, Db, J, C>;

/// EVM with default env types and adjustable DB.
pub type Evm<Db, Insp = NoOpInspector, Inst = Instructions<Db>, Prec = EthPrecompiles> =
    revm::context::Evm<Ctx<Db>, Insp, Inst, Prec>;

/// Handler table for EVM opcodes.
pub type Instructions<Db> = EthInstructions<EthInterpreter, Ctx<Db>>;

/// The handler type for an EVM opcode.
pub type Instruction<Db> = revm::interpreter::Instruction<EthInterpreter, Ctx<Db>>;
