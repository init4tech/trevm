use crate::{evm::Trevm, helpers::Ctx, states::EvmNeedsCfg};
use revm::{
    database::in_memory_db::InMemoryDB, handler::EthPrecompiles, inspector::NoOpInspector,
    precompile::Precompiles, primitives::hardfork::SpecId, Database, Inspector, MainBuilder,
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
    pub(crate) precompiles: Option<&'static Precompiles>,
}

impl TrevmBuilder<InMemoryDB, NoOpInspector> {
    /// Create a new builder with the default database and inspector.
    #[allow(clippy::new_without_default)] // default would make bad devex :(
    pub const fn new() -> Self {
        Self { db: None, insp: NoOpInspector, spec: SpecId::PRAGUE, precompiles: None }
    }
}

impl<Db, Insp> TrevmBuilder<Db, Insp> {
    /// Set the database for the EVM.
    pub fn with_db<Odb>(self, db: Odb) -> TrevmBuilder<Odb, Insp>
    where
        Db: Database,
    {
        TrevmBuilder {
            db: Some(db),
            insp: self.insp,
            spec: self.spec,
            precompiles: self.precompiles,
        }
    }

    /// Set the inspector for the EVM.
    pub fn with_insp<OInsp>(self, insp: OInsp) -> TrevmBuilder<Db, OInsp> {
        TrevmBuilder { db: self.db, insp, spec: self.spec, precompiles: self.precompiles }
    }

    /// Set the spec id for the EVM.
    pub const fn with_spec_id(mut self, spec: SpecId) -> Self {
        self.spec = spec;
        self
    }

    /// Set the precompiles for the EVM.
    ///
    /// The precompiles must be a static reference to a precompiles instance.
    /// If not using a built-in [`Precompiles`], it is generally recommended to
    /// use a `OnceLock` to create this borrow.
    pub const fn with_precompiles(mut self, precompiles: &'static Precompiles) -> Self {
        self.precompiles = Some(precompiles);
        self
    }

    /// Set the precompiles for the EVM from the current spec id.
    pub fn with_precompiles_from_spec(mut self) -> Self {
        self.precompiles = Some(Precompiles::new(self.spec.into()));
        self
    }

    /// Build the Trevm instance.
    pub fn build_trevm(self) -> Result<EvmNeedsCfg<Db, Insp>, TrevmBuilderError>
    where
        Db: Database,
        Insp: Inspector<Ctx<Db>>,
    {
        let db = self.db.ok_or(TrevmBuilderError::DatabaseNotSet)?;
        let ctx = Ctx::new(db, self.spec);

        let mut evm = ctx.build_mainnet_with_inspector(self.insp);

        if let Some(precompiles) = self.precompiles {
            evm.precompiles = EthPrecompiles { precompiles, spec: self.spec };
        }

        Ok(Trevm::from(evm))
    }
}
