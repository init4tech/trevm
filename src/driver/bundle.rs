use crate::{helpers::Ctx, states::EvmBundleDriverErrored, EvmNeedsTx};
use revm::{context::result::EVMError, Database, DatabaseCommit, Inspector};

/// The result of driving a bundle to completion.
pub type DriveBundleResult<Db, Insp, T> =
    Result<EvmNeedsTx<Db, Insp>, EvmBundleDriverErrored<Db, Insp, T>>;

/// Driver for a bundle of transactions. This trait allows a type to specify the
/// entire lifecycle of a bundle, simulating the entire list of transactions.
pub trait BundleDriver<Db, Insp>
where
    Db: Database + DatabaseCommit,
    Insp: Inspector<Ctx<Db>>,
{
    /// An error type for this driver.
    type Error: core::error::Error + From<EVMError<Db::Error>>;

    /// Run the transactions contained in the bundle.
    fn run_bundle(&mut self, trevm: EvmNeedsTx<Db, Insp>) -> DriveBundleResult<Db, Insp, Self>;

    /// Run post
    fn post_bundle(&mut self, trevm: &EvmNeedsTx<Db, Insp>) -> Result<(), Self::Error>;
}
