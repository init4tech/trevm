use crate::{evm::Trevm, helpers::Ctx, states::EvmNeedsCfg};
use revm::{
    database::in_memory_db::InMemoryDB, primitives::hardfork::SpecId, Database, MainBuilder,
};

/// Error that can occur when building a Trevm instance.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum TrevmBuilderError {
    /// Database not set.
    #[error("Database not set")]
    DatabaseNotSet,
}

/// A builder for [`Trevm`] that allows configuring the EVM.
#[derive(Debug, Clone)]
pub struct TrevmBuilder<Db, Insp> {
    pub(crate) db: Option<Db>,
    pub(crate) insp: Insp,
    pub(crate) spec: SpecId,
}

impl TrevmBuilder<InMemoryDB, ()> {
    /// Create a new builder with the default database and inspector.
    #[allow(clippy::new_without_default)] // default would make bad devex :(
    pub const fn new() -> Self {
        Self { db: None, insp: (), spec: SpecId::PRAGUE }
    }
}

impl<Db, Insp> TrevmBuilder<Db, Insp> {
    /// Set the database for the EVM.
    pub fn with_db<Odb>(self, db: Odb) -> TrevmBuilder<Odb, Insp>
    where
        Db: Database,
    {
        TrevmBuilder { db: Some(db), insp: self.insp, spec: self.spec }
    }

    /// Set the inspector for the EVM.
    pub fn with_insp<OInsp>(self, insp: OInsp) -> TrevmBuilder<Db, OInsp> {
        TrevmBuilder { db: self.db, insp, spec: self.spec }
    }

    /// Set the spec id for the EVM.
    pub const fn with_spec_id(mut self, spec: SpecId) -> Self {
        self.spec = spec;
        self
    }

    /// Build the Trevm instance.
    pub fn build_trevm(self) -> Result<EvmNeedsCfg<Db, Insp>, TrevmBuilderError>
    where
        Db: Database,
    {
        let db = self.db.ok_or(TrevmBuilderError::DatabaseNotSet)?;
        let ctx = Ctx::new(db, self.spec);
        let evm = ctx.build_mainnet_with_inspector(self.insp);
        Ok(Trevm::from(evm))
    }
}
