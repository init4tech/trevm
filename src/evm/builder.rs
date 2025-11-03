use crate::{evm::Trevm, helpers::Ctx, EvmNeedsCfg};
use revm::{
    handler::EthPrecompiles, inspector::NoOpInspector, precompile::Precompiles,
    primitives::hardfork::SpecId, Database, Inspector, MainBuilder,
};

/// Error that can occur when building a Trevm instance.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum TrevmBuilderError {
    /// Database not set.
    #[error("Database not set")]
    DatabaseNotSet,
}

#[allow(unnameable_types)]
#[derive(Debug, Copy, Clone)]
pub struct BuilderNeedsDb {
    _private: (),
}

#[allow(unnameable_types)]
#[derive(Debug, Copy, Clone)]
pub struct BuilderReady<Db> {
    db: Db,
}

/// A builder for [`Trevm`] that allows configuring the EVM.
#[derive(Debug, Clone)]
pub struct TrevmBuilder<Insp, State = BuilderNeedsDb> {
    pub(crate) insp: Insp,
    pub(crate) spec: SpecId,
    pub(crate) precompiles: Option<&'static Precompiles>,
    pub(crate) state: State,
}

impl TrevmBuilder<NoOpInspector> {
    /// Create a new builder with the default database and inspector.
    #[allow(clippy::new_without_default)] // default would make bad devex :(
    pub const fn new() -> Self {
        Self {
            insp: NoOpInspector,
            spec: SpecId::PRAGUE,
            precompiles: None,
            state: BuilderNeedsDb { _private: () },
        }
    }
}

impl<Insp, State> TrevmBuilder<Insp, State> {
    /// Set the database for the EVM.
    pub fn with_db<Odb>(self, db: Odb) -> TrevmBuilder<Insp, BuilderReady<Odb>>
    where
        Odb: Database,
    {
        TrevmBuilder {
            insp: self.insp,
            spec: self.spec,
            precompiles: self.precompiles,
            state: BuilderReady { db },
        }
    }

    /// Set the inspector for the EVM.
    ///
    /// Equivalent to [`Self::with_inspector`].
    pub fn with_insp<OInsp>(self, insp: OInsp) -> TrevmBuilder<OInsp, State> {
        TrevmBuilder { insp, spec: self.spec, precompiles: self.precompiles, state: self.state }
    }

    /// Set the inspector for the EVM.
    ///
    /// Equivalent to [`Self::with_insp`].
    pub fn with_inspector<OInsp>(self, insp: OInsp) -> TrevmBuilder<OInsp, State> {
        self.with_insp(insp)
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
}

impl<Insp, Db> TrevmBuilder<Insp, BuilderReady<Db>> {
    /// Build the Trevm instance.
    pub fn build_trevm(self) -> EvmNeedsCfg<Db, Insp>
    where
        Db: Database,
        Insp: Inspector<Ctx<Db>>,
    {
        let db = self.state.db;
        let ctx = Ctx::new(db, self.spec);

        let mut evm = ctx.build_mainnet_with_inspector(self.insp);

        if let Some(precompiles) = self.precompiles {
            evm.precompiles = EthPrecompiles { precompiles, spec: self.spec };
        }

        Trevm::from(evm)
    }
}

// Some code above and documentation is adapted from the revm crate, and is
// reproduced here under the terms of the MIT license.
//
// MIT License
//
// Copyright (c) 2021-2024 draganrakita
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

// Some code above is reproduced from `reth`. It is reused here under the MIT
// license.
//
// The MIT License (MIT)
//
// Copyright (c) 2022-2024 Reth Contributors
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.
