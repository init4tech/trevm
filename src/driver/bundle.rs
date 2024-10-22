use crate::{states::EvmBundleDriverErrored, EvmNeedsTx};
use revm::{primitives::EVMError, Database, DatabaseCommit};

/// The result of driving a bundle to completion.
pub type DriveBundleResult<'a, Ext, Db, T> =
    Result<EvmNeedsTx<'a, Ext, Db>, EvmBundleDriverErrored<'a, Ext, Db, T>>;

/// Driver for a bundle of transactions. This trait allows a type to specify the
/// entire lifecycle of a bundle, simulating the entire list of transactions.
pub trait BundleDriver<Ext> {
    /// An error type for this driver.
    type Error<Db: Database>: core::error::Error + From<EVMError<Db::Error>>;

    /// Run the transactions contained in the bundle.
    fn run_bundle<'a, Db: Database + DatabaseCommit>(
        &mut self,
        trevm: EvmNeedsTx<'a, Ext, Db>,
    ) -> DriveBundleResult<'a, Ext, Db, Self>;

    /// Run post
    fn post_bundle<Db: Database + DatabaseCommit>(
        &mut self,
        trevm: &EvmNeedsTx<'_, Ext, Db>,
    ) -> Result<(), Self::Error<Db>>;
}
