use crate::{
    helpers::{Ctx, Evm},
    EvmNeedsCfg, NeedsCfg,
};
use core::fmt;
use revm::{inspector::NoOpInspector, Database, Inspector};

/// Trevm provides a type-safe interface to the EVM, using the typestate pattern.
///
/// See the [crate-level documentation](crate) for more information.
pub struct Trevm<Db, Insp = NoOpInspector, TrevmState = NeedsCfg>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    pub(crate) inner: Box<Evm<Db, Insp>>,
    pub(crate) state: TrevmState,
}

impl<Db, Insp, TrevmState> fmt::Debug for Trevm<Db, Insp, TrevmState>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Trevm").finish_non_exhaustive()
    }
}

impl<Db, Insp, TrevmState> AsRef<Evm<Db, Insp>> for Trevm<Db, Insp, TrevmState>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    fn as_ref(&self) -> &Evm<Db, Insp> {
        &self.inner
    }
}

impl<Db, Insp> From<Evm<Db, Insp>> for EvmNeedsCfg<Db, Insp>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    fn from(inner: Evm<Db, Insp>) -> Self {
        Self { inner: Box::new(inner), state: NeedsCfg::new() }
    }
}
