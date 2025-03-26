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
pub type Evm<
    Db,
    Insp = NoOpInspector,
    Inst = EthInstructions<EthInterpreter, Ctx<Db>>,
    Prec = EthPrecompiles,
> = revm::context::Evm<Ctx<Db>, Insp, Inst, Prec>;
