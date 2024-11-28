use revm::{
    primitives::{BlockEnv, CfgEnv, TxEnv},
    Database, Evm,
};

/// Types that can fill the EVM transaction environment [`TxEnv`].
pub trait Tx: Send + Sync {
    /// Fill the transaction environment.
    ///
    /// ## Note:
    ///
    /// It is generally expected that the filler will fill (or at least
    /// inspect) ALL fields of the transaction environment. This is because
    /// the EVM will NOT clear the transaction environment between
    /// transactions. If the filler does not fill a field, it will be left
    /// unchanged from the previous transaction.
    fn fill_tx_env(&self, tx_env: &mut TxEnv);

    /// Fill the transaction environment on the EVM.
    fn fill_tx<Ext, Db: Database>(&self, evm: &mut Evm<'_, Ext, Db>) {
        let tx_env: &mut TxEnv = evm.tx_mut();
        self.fill_tx_env(tx_env);
    }
}
/// Types that can fill the EVM block environment [`BlockEnv`].
pub trait Block: Send + Sync {
    /// Fill the block environment.
    ///
    /// ## Note:
    ///
    /// It is generally expected that the filler will fill (or at least
    /// inspect) ALL fields of the block environment. This is because the EVM
    /// will NOT clear the block environment between blocks. If the filler does
    /// not fill a field, it will be left unchanged from the previous block.
    fn fill_block_env(&self, block_env: &mut BlockEnv);

    /// Fill the block environment on the EVM.
    fn fill_block<Ext, Db: Database>(&self, evm: &mut Evm<'_, Ext, Db>) {
        let block_env: &mut BlockEnv = evm.block_mut();
        self.fill_block_env(block_env);
    }

    /// Get the transaction count hint from the filler. This can be used for
    /// memory pre-allocation during block execution.
    fn tx_count_hint(&self) -> Option<usize> {
        None
    }
}

/// Types that can fill the EVM configuration environment [`CfgEnv`].
///
/// Because the CFG env has quite a few conditionally compiled properties, it
/// is recommended to use the default implementation of `fill_cfg_env` to ensure
/// that fields are filled only when appropriate.
///
/// Note that the following properties on [`CfgEnv`] are feature-gated:
/// - `kzg_settings` - gated by `c-kzg`
/// - `memory_limit` - gated by `memory_limit`
/// - `disable_balance_check` - gated by `optional_balance_check`
/// - `disable_block_gas_limit` - gated by `optional_block_gas_limit`
/// - `disable_eip3607` - gated by `optional_eip3607`
/// - `disable_gas_refund` - gated by `optional_gas_refund`
/// - `disable_base_fee` - gated by `optional_no_base_fee`
/// - `disable_beneficiary_reward` - gated by `optional_beneficiary_reward`
///
/// Cfg fillers should consider these feature gates when implementing the trait.
pub trait Cfg: Send + Sync {
    /// Fill the configuration environment.
    fn fill_cfg_env(&self, cfg_env: &mut CfgEnv);

    /// Fill the configuration environment on the EVM.
    fn fill_cfg<Ext, Db: Database>(&self, evm: &mut Evm<'_, Ext, Db>) {
        let cfg_env: &mut CfgEnv = evm.cfg_mut();
        self.fill_cfg_env(cfg_env);
    }
}

#[cfg(test)]
mod test {
    use alloy::consensus::constants::GWEI_TO_WEI;
    use alloy_primitives::{B256, U256};
    use revm::primitives::{BlobExcessGasAndPrice, BlockEnv, CfgEnv};

    use super::*;

    impl Block for () {
        fn fill_block_env(&self, block_env: &mut BlockEnv) {
            let BlockEnv {
                number,
                coinbase,
                timestamp,
                gas_limit,
                basefee,
                difficulty,
                prevrandao,
                blob_excess_gas_and_price,
            } = block_env;
            *number = U256::from(1);
            *coinbase = Default::default();
            *timestamp = U256::from(1720450148); // Time when I was writing the test code
            *gas_limit = U256::from(30_000_000);
            *basefee = U256::from(5 * GWEI_TO_WEI);

            let diff = B256::repeat_byte(0xab);
            *prevrandao = Some(diff);
            *difficulty = U256::from_be_bytes(diff.into());
            *blob_excess_gas_and_price = Some(BlobExcessGasAndPrice::new(1_000_000));
        }

        fn tx_count_hint(&self) -> Option<usize> {
            None
        }
    }

    impl Cfg for () {
        fn fill_cfg_env(&self, cfg_env: &mut CfgEnv) {
            let CfgEnv { chain_id, .. } = cfg_env;
            *chain_id = 1;
        }
    }
}
