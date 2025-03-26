use crate::{states::EvmBundleDriverErrored, EvmNeedsTx};
use revm::{context::result::EVMError, Database, DatabaseCommit};

/// The result of driving a bundle to completion.
pub type DriveBundleResult<Db, Insp, T> =
    Result<EvmNeedsTx<Db, Insp>, EvmBundleDriverErrored<Db, Insp, T>>;

/// Driver for a bundle of transactions. This trait allows a type to specify the
/// entire lifecycle of a bundle, simulating the entire list of transactions.
pub trait BundleDriver<Insp> {
    /// An error type for this driver.
    type Error<Db: Database + DatabaseCommit>: core::error::Error + From<EVMError<Db::Error>>;

    /// Run the transactions contained in the bundle.
    fn run_bundle<Db>(&mut self, trevm: EvmNeedsTx<Db, Insp>) -> DriveBundleResult<Db, Insp, Self>
    where
        Db: Database + DatabaseCommit;

    /// Run post
    fn post_bundle<Db>(&mut self, trevm: &EvmNeedsTx<Db, Insp>) -> Result<(), Self::Error<Db>>
    where
        Db: Database + DatabaseCommit;
}
