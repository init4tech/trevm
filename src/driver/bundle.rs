use crate::{helpers::Ctx, BundleError, EvmBundleDriverErrored, EvmNeedsTx};
use alloy::{
    consensus::{
        transaction::{Recovered, SignerRecoverable},
        TxEnvelope,
    },
    eips::Decodable2718,
};
use revm::{
    context::result::EVMError, inspector::NoOpInspector, Database, DatabaseCommit, Inspector,
};

/// The result of driving a bundle to completion.
pub type DriveBundleResult<T, Db, Insp> =
    Result<EvmNeedsTx<Db, Insp>, EvmBundleDriverErrored<T, Db, Insp>>;

/// Driver for a bundle of transactions. This trait allows a type to specify the
/// entire lifecycle of a bundle, simulating the entire list of transactions.
pub trait BundleDriver<Db, Insp = NoOpInspector>
where
    Db: Database + DatabaseCommit,
    Insp: Inspector<Ctx<Db>>,
{
    /// An error type for this driver.
    type Error: core::error::Error + From<EVMError<Db::Error>>;

    /// Get an iterator over the raw transaction bytes in this bundle.
    fn transactions(&self) -> impl IntoIterator<Item = &[u8]>;

    /// Recover the transactions in this bundle.
    fn recovered_transactions(
        &self,
    ) -> impl IntoIterator<Item = Result<Recovered<TxEnvelope>, BundleError<Db>>>
    where
        Self: Sized,
        Db: Database,
    {
        self.transactions().into_iter().map(|tx_bytes| {
            TxEnvelope::decode_2718_exact(tx_bytes)
                .map_err(BundleError::TransactionDecoding)
                .and_then(|envelope| {
                    envelope.try_into_recovered().map_err(BundleError::TransactionSenderRecovery)
                })
        })
    }

    /// Run the transactions contained in the bundle.
    fn run_bundle(&mut self, trevm: EvmNeedsTx<Db, Insp>) -> DriveBundleResult<Self, Db, Insp>;

    /// Run post
    fn post_bundle(&mut self, trevm: &EvmNeedsTx<Db, Insp>) -> Result<(), Self::Error>;
}
