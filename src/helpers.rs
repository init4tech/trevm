use revm::{
    context::{BlockEnv, CfgEnv, ContextTr, TxEnv},
    handler::{instructions::EthInstructions, EthPrecompiles},
    inspector::NoOpInspector,
    interpreter::interpreter::EthInterpreter,
    Context, Database, DatabaseCommit, DatabaseRef, Journal,
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

/// A trait for contexts that can be used with `Trevm`.
pub trait TrevmCtx:
    ContextTr<
    Block = BlockEnv,
    Tx = TxEnv,
    Cfg = CfgEnv,
    Db: Database,
    Journal = Journal<<Self as ContextTr>::Db>,
    Chain = (),
>
{
}

impl<T> TrevmCtx for T where
    T: ContextTr<
        Block = BlockEnv,
        Tx = TxEnv,
        Cfg = CfgEnv,
        Db: Database,
        Journal = Journal<<Self as ContextTr>::Db>,
        Chain = (),
    >
{
}

/// A trait for contexts that can be used with `Trevm` and support committing.
pub trait TrevmCtxCommit: TrevmCtx + ContextTr<Db: DatabaseCommit> {}
impl<T> TrevmCtxCommit for T where T: TrevmCtx + ContextTr<Db: DatabaseCommit> {}

/// A trait for contexts that can be used with `Trevm` and support committing.
pub trait TrevmCtxRef: TrevmCtx + ContextTr<Db: DatabaseRef> {}
impl<T> TrevmCtxRef for T where T: TrevmCtx + ContextTr<Db: DatabaseRef> {}
