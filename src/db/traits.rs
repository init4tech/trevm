use revm::{
    db::{states::bundle_state::BundleRetention, BundleState, State},
    primitives::{Account, Address, B256},
    Database, DatabaseCommit,
};
use std::{collections::BTreeMap, convert::Infallible, sync::Arc};

/// Abstraction trait covering types that accumulate state changes into a
/// [`BundleState`]. The prime example of this is [`State`]. These types are
/// use to accumulate state changes during the execution of a sequence of
/// transactions, and then provide access to the net changes in the form of a
/// [`BundleState`].
pub trait StateAcc {
    /// Set the state clear flag. See [`State::set_state_clear_flag`].
    fn set_state_clear_flag(&mut self, flag: bool);

    /// Merge transitions into the bundle. See [`State::merge_transitions`].
    fn merge_transitions(&mut self, retention: BundleRetention);

    /// Take the bundle. See [`State::take_bundle`].
    fn take_bundle(&mut self) -> BundleState;

    /// Set the block hashes, overriding any existing values, and inserting any
    /// absent values.
    fn set_block_hashes(&mut self, block_hashes: &BTreeMap<u64, B256>);
}

impl<Db: Database> StateAcc for State<Db> {
    fn set_state_clear_flag(&mut self, flag: bool) {
        Self::set_state_clear_flag(self, flag)
    }

    fn merge_transitions(&mut self, retention: BundleRetention) {
        Self::merge_transitions(self, retention)
    }

    fn take_bundle(&mut self) -> BundleState {
        Self::take_bundle(self)
    }

    fn set_block_hashes(&mut self, block_hashes: &BTreeMap<u64, B256>) {
        self.block_hashes.extend(block_hashes)
    }
}

/// Fallible version of [`StateAcc`].
///
/// Abstraction trait covering types that accumulate state changes into a
/// [`BundleState`]. The prime example of this is [`State`]. These types are
/// use to accumulate state changes during the execution of a sequence of
/// transactions, and then provide access to the net changes in the form of a
/// [`BundleState`].
///
/// The primary motivator for this trait is to allow for the implementation of
/// [`StateAcc`] for [`Arc`]-wrapped DBs, which may fail to mutate if the
/// reference is not unique.
pub trait TryStateAcc: Sync {
    /// Error type to be thrown when state accumulation fails.
    type Error: core::error::Error;

    /// Attempt to set the state clear flag. See [`State::set_state_clear_flag`].
    fn try_set_state_clear_flag(&mut self, flag: bool) -> Result<(), Self::Error>;

    /// Attempt to merge transitions into the bundle. See
    /// [`State::merge_transitions`].
    fn try_merge_transitions(&mut self, retention: BundleRetention) -> Result<(), Self::Error>;

    /// Attempt to take the bundle. See [`State::take_bundle`].
    fn try_take_bundle(&mut self) -> Result<BundleState, Self::Error>;

    /// Attempt to set the block hashes, overriding any existing values, and
    /// inserting any absent values.
    fn try_set_block_hashes(
        &mut self,
        block_hashes: &BTreeMap<u64, B256>,
    ) -> Result<(), Self::Error>;
}

impl<Db> TryStateAcc for Db
where
    Db: StateAcc + Sync,
{
    type Error = Infallible;

    fn try_set_state_clear_flag(&mut self, flag: bool) -> Result<(), Infallible> {
        self.set_state_clear_flag(flag);
        Ok(())
    }

    fn try_merge_transitions(&mut self, retention: BundleRetention) -> Result<(), Infallible> {
        self.merge_transitions(retention);
        Ok(())
    }

    fn try_take_bundle(&mut self) -> Result<BundleState, Infallible> {
        Ok(self.take_bundle())
    }

    fn try_set_block_hashes(
        &mut self,
        block_hashes: &BTreeMap<u64, B256>,
    ) -> Result<(), Infallible> {
        self.set_block_hashes(block_hashes);
        Ok(())
    }
}

/// Error type for implementation of [`TryStateAcc`] for [`Arc`]-wrapped
/// DBs.
#[derive(thiserror::Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArcUpgradeError {
    /// Arc reference is not unique. Ensure that all other references are
    /// dropped before attempting to mutate the state.
    #[error("Arc reference is not unique, cannot mutate")]
    NotUnique,
}

impl<Db> TryStateAcc for Arc<Db>
where
    Db: StateAcc + Sync + Send,
{
    type Error = ArcUpgradeError;

    fn try_set_state_clear_flag(&mut self, flag: bool) -> Result<(), ArcUpgradeError> {
        Self::get_mut(self).ok_or(ArcUpgradeError::NotUnique)?.set_state_clear_flag(flag);
        Ok(())
    }

    fn try_merge_transitions(&mut self, retention: BundleRetention) -> Result<(), ArcUpgradeError> {
        Self::get_mut(self).ok_or(ArcUpgradeError::NotUnique)?.merge_transitions(retention);
        Ok(())
    }

    fn try_take_bundle(&mut self) -> Result<BundleState, ArcUpgradeError> {
        Ok(Self::get_mut(self).ok_or(ArcUpgradeError::NotUnique)?.take_bundle())
    }

    fn try_set_block_hashes(
        &mut self,
        block_hashes: &BTreeMap<u64, B256>,
    ) -> Result<(), ArcUpgradeError> {
        Self::get_mut(self).ok_or(ArcUpgradeError::NotUnique)?.set_block_hashes(block_hashes);
        Ok(())
    }
}

/// A fallible version of [`DatabaseCommit`].
pub trait TryDatabaseCommit {
    /// Error type to be thrown when committing changes fails.
    type Error: core::error::Error;

    /// Attempt to commit changes to the database.
    fn try_commit(
        &mut self,
        changes: revm::primitives::HashMap<Address, Account>,
    ) -> Result<(), Self::Error>;
}

impl<Db> TryDatabaseCommit for Arc<Db>
where
    Db: DatabaseCommit,
{
    type Error = ArcUpgradeError;

    fn try_commit(
        &mut self,
        changes: revm::primitives::HashMap<Address, Account>,
    ) -> Result<(), Self::Error> {
        Self::get_mut(self).ok_or(ArcUpgradeError::NotUnique)?.commit(changes);
        Ok(())
    }
}
