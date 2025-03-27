use super::{checked_insert_code, execute_system_tx};
use crate::{system::SystemTx, EvmNeedsTx};
use alloy::primitives::{Address, Bytes, B256, U256};
use revm::{context::result::EVMError, primitives::hardfork::SpecId, Database, DatabaseCommit};

/// The number of beacon roots to store in the beacon roots contract.
pub const HISTORY_BUFFER_LENGTH: u64 = 8191;

pub use alloy::eips::eip4788::{BEACON_ROOTS_ADDRESS, BEACON_ROOTS_CODE};

impl SystemTx {
    /// Instantiate a system call for the pre-block beacon roots as specified in
    /// [EIP-4788].
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn eip4788(parent_beacon_root: B256) -> Self {
        Self::eip4788_with_target(parent_beacon_root, BEACON_ROOTS_ADDRESS)
    }

    /// Instantiate a system call for the pre-block beacon roots as specified in
    /// [EIP-4788], with a custom target address.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn eip4788_with_target(parent_beacon_root: B256, target: Address) -> Self {
        Self::new(target, Bytes::from(parent_beacon_root))
    }

    /// Instantiate a system call for the pre-block beacon roots as specified in
    /// [EIP-4788], with a custom target address and caller address.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn eip4788_with_target_and_caller(
        parent_beacon_root: B256,
        target: Address,
        caller: Address,
    ) -> Self {
        Self::new_with_caller(target, Bytes::from(parent_beacon_root), caller)
    }
}

/// The slot for the [EIP-4788] timestamp storage.
///
/// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
pub fn eip4788_timestamp_slot(timestamp: u64) -> U256 {
    U256::from(timestamp % HISTORY_BUFFER_LENGTH)
}

/// The slot for the [EIP-4788] root storage.
///
/// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
pub fn eip4788_root_slot(timestamp: u64) -> U256 {
    eip4788_timestamp_slot(timestamp) + U256::from(HISTORY_BUFFER_LENGTH)
}

impl<Db: Database + DatabaseCommit, Insp> EvmNeedsTx<Db, Insp> {
    /// Apply a system transaction as specified in [EIP-4788]. The EIP-4788
    /// pre-block action was introduced in Cancun, and calls the beacon root
    /// contract to update the historical beacon root.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn apply_eip4788(&mut self, parent_beacon_root: B256) -> Result<(), EVMError<Db::Error>> {
        if self.spec_id() < SpecId::CANCUN {
            return Ok(());
        }

        checked_insert_code(self.inner_mut_unchecked(), BEACON_ROOTS_ADDRESS, &BEACON_ROOTS_CODE)?;
        execute_system_tx(self.inner_mut_unchecked(), &SystemTx::eip4788(parent_beacon_root))
            .map(drop)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{NoopBlock, NoopCfg};
    use alloy::primitives::U256;
    use revm::bytecode::Bytecode;

    #[test]
    fn test_eip4788() {
        let timestamp = 8;

        let mut trevm = crate::test_utils::test_trevm().fill_cfg(&NoopCfg).fill_block(&NoopBlock);

        trevm.inner_mut_unchecked().modify_block(|block| {
            block.timestamp = timestamp;
        });

        let parent_beacon_root = B256::repeat_byte(0xaa);

        trevm.apply_eip4788(parent_beacon_root).unwrap();

        let ts_slot = eip4788_timestamp_slot(timestamp);
        let root_slot = eip4788_root_slot(timestamp);

        assert_eq!(
            trevm.try_read_storage(BEACON_ROOTS_ADDRESS, ts_slot).unwrap(),
            U256::from(timestamp)
        );
        assert_eq!(
            trevm.try_read_storage(BEACON_ROOTS_ADDRESS, root_slot).unwrap(),
            parent_beacon_root.into()
        );
        assert_eq!(
            trevm.try_read_code(BEACON_ROOTS_ADDRESS).unwrap().unwrap(),
            Bytecode::new_raw(BEACON_ROOTS_CODE.clone()),
        );
    }
}
