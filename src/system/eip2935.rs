use crate::EvmNeedsTx;
use alloy_primitives::U256;
use revm::{
    primitives::{EVMError, SpecId, BLOCKHASH_SERVE_WINDOW},
    Database, DatabaseCommit,
};

pub use alloy_eips::eip2935::{HISTORY_STORAGE_ADDRESS, HISTORY_STORAGE_CODE};

use super::checked_insert_code;

/// The slot for the [EIP-2935] blockhash storage.
///
/// [EIP-2935]: https://eips.ethereum.org/EIPS/eip-2935
pub fn eip2935_slot(block_num: u64) -> U256 {
    U256::from(block_num % BLOCKHASH_SERVE_WINDOW as u64)
}

impl<'a, Ext, Db: Database + DatabaseCommit> EvmNeedsTx<'a, Ext, Db> {
    /// Apply the pre-block logic for [EIP-2935]. This logic was introduced in
    /// Prague and updates historical block hashes in a special system
    /// contract. Unlike other system actions, this is NOT modeled as a
    /// transaction.
    ///
    /// [EIP-2935]: https://eips.ethereum.org/EIPS/eip-2935
    pub fn apply_eip2935(&mut self) -> Result<(), EVMError<Db::Error>> {
        if self.spec_id() < SpecId::PRAGUE || self.inner().block().number.is_zero() {
            return Ok(());
        }

        checked_insert_code(
            self.inner_mut_unchecked(),
            HISTORY_STORAGE_ADDRESS,
            &HISTORY_STORAGE_CODE,
        )?;

        let block_num = self.inner().block().number.as_limbs()[0];
        let prev_block = block_num.saturating_sub(1);

        // Update the EVM state with the new value.
        let slot = eip2935_slot(prev_block);

        let parent_block_hash = self
            .inner_mut_unchecked()
            .db_mut()
            .block_hash(prev_block)
            .map_err(EVMError::Database)?;

        dbg!(slot);
        dbg!(parent_block_hash);

        self.try_set_storage_unchecked(HISTORY_STORAGE_ADDRESS, slot, parent_block_hash.into())
            .map_err(EVMError::Database)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{NoopBlock, NoopCfg};
    use alloy_primitives::B256;
    use revm::primitives::Bytecode;

    #[test]
    fn test_eip2935() {
        let block_num = U256::from(5);
        let prev_block_num = U256::from(4);
        let prev_hash = B256::repeat_byte(0xaa);
        let slot = eip2935_slot(prev_block_num.to());

        // we create a trevm instance with the block number set to 1
        let mut trevm = crate::test_utils::test_trevm().fill_cfg(&NoopCfg).fill_block(&NoopBlock);
        trevm.inner_mut_unchecked().block_mut().number = block_num;

        // we set the previous block hash in the cachedb, as it will be loaded
        // during eip application
        trevm.inner_mut_unchecked().db_mut().block_hashes.insert(prev_block_num, prev_hash);

        trevm.apply_eip2935().unwrap();

        assert_eq!(
            trevm.try_read_storage(HISTORY_STORAGE_ADDRESS, slot).unwrap(),
            prev_hash.into()
        );
        assert_eq!(
            trevm.try_read_code(HISTORY_STORAGE_ADDRESS).unwrap().unwrap(),
            Bytecode::new_raw(HISTORY_STORAGE_CODE.clone())
        );
    }
}