use crate::{helpers::TrevmCtxCommit, states::EvmBundleDriverErrored, EvmNeedsTx};
use revm::{context::result::EVMError, Database, DatabaseCommit};

/// The result of driving a bundle to completion.
pub type DriveBundleResult<Ctx, Insp, Inst, Prec, T> =
    Result<EvmNeedsTx<Ctx, Insp, Inst, Prec>, EvmBundleDriverErrored<Ctx, Insp, Inst, Prec, T>>;

/// Driver for a bundle of transactions. This trait allows a type to specify the
/// entire lifecycle of a bundle, simulating the entire list of transactions.
pub trait BundleDriver<Insp> {
    /// An error type for this driver.
    type Error<Db: Database + DatabaseCommit>: core::error::Error + From<EVMError<Db::Error>>;

    /// Run the transactions contained in the bundle.
    fn run_bundle<'a, Ctx, Inst, Prec>(
        &mut self,
        trevm: EvmNeedsTx<Ctx, Insp, Inst, Prec>,
    ) -> DriveBundleResult<Ctx, Insp, Inst, Prec, Self>
    where
        Ctx: TrevmCtxCommit;

    /// Run post
    fn post_bundle<Ctx, Inst, Prec>(
        &mut self,
        trevm: &EvmNeedsTx<Ctx, Insp, Inst, Prec>,
    ) -> Result<(), Self::Error<Ctx::Db>>
    where
        Ctx: TrevmCtxCommit;
}
