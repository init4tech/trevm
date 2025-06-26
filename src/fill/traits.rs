use crate::helpers::Ctx;
use revm::{
    context::{BlockEnv, CfgEnv, Evm, TxEnv},
    Database,
};
use std::sync::Arc;

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
    fn fill_tx<Db: Database, Insp, Inst, Prec, Frame>(&self, evm: &mut Evm<Ctx<Db>, Insp, Inst, Prec, Frame>)
    where
        Self: Sized,
    {
        evm.ctx.modify_tx(|tx_env| self.fill_tx_env(tx_env));
    }
}

impl Tx for TxEnv {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        *tx_env = self.clone();
    }
}

impl Tx for Arc<dyn Tx> {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        self.as_ref().fill_tx_env(tx_env);
    }
}

impl Tx for Box<dyn Tx> {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        self.as_ref().fill_tx_env(tx_env);
    }
}

impl<T> Tx for T
where
    T: Fn(&mut TxEnv) + Send + Sync,
{
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        self(tx_env);
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
    fn fill_block<Db: Database, Insp, Inst, Prec, Frame>(&self, evm: &mut Evm<Ctx<Db>, Insp, Inst, Prec, Frame>)
    where
        Self: Sized,
    {
        evm.ctx.modify_block(|block_env| self.fill_block_env(block_env));
    }

    /// Get the transaction count hint from the filler. This can be used for
    /// memory pre-allocation during block execution.
    fn tx_count_hint(&self) -> Option<usize> {
        None
    }
}

impl<T> Block for T
where
    T: Fn(&mut BlockEnv) + Send + Sync,
{
    fn fill_block_env(&self, block_env: &mut BlockEnv) {
        self(block_env);
    }
}

impl Block for BlockEnv {
    fn fill_block_env(&self, block_env: &mut BlockEnv) {
        *block_env = self.clone();
    }
}

impl Block for Arc<dyn Block> {
    fn fill_block_env(&self, block_env: &mut BlockEnv) {
        self.as_ref().fill_block_env(block_env);
    }
}

impl Block for Box<dyn Block> {
    fn fill_block_env(&self, block_env: &mut BlockEnv) {
        self.as_ref().fill_block_env(block_env);
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
    fn fill_cfg<Db: Database, Insp, Inst, Prec, Frame>(&self, evm: &mut Evm<Ctx<Db>, Insp, Inst, Prec, Frame>)
    where
        Self: Sized,
    {
        evm.ctx.modify_cfg(|cfg_env| self.fill_cfg_env(cfg_env));
    }
}

impl Cfg for Arc<dyn Cfg> {
    fn fill_cfg_env(&self, cfg_env: &mut CfgEnv) {
        self.as_ref().fill_cfg_env(cfg_env);
    }
}

impl Cfg for CfgEnv {
    fn fill_cfg_env(&self, cfg_env: &mut CfgEnv) {
        *cfg_env = self.clone();
    }
}

impl Cfg for Box<dyn Cfg> {
    fn fill_cfg_env(&self, cfg_env: &mut CfgEnv) {
        self.as_ref().fill_cfg_env(cfg_env);
    }
}

impl<T> Cfg for T
where
    T: Fn(&mut CfgEnv) + Send + Sync,
{
    fn fill_cfg_env(&self, cfg_env: &mut CfgEnv) {
        self(cfg_env);
    }
}

#[cfg(test)]
mod test {
    use alloy::{
        consensus::constants::GWEI_TO_WEI,
        primitives::{B256, U256},
    };
    use revm::{
        context::{BlockEnv, CfgEnv},
        context_interface::block::BlobExcessGasAndPrice,
    };

    use super::*;

    #[allow(dead_code)]
    fn object_safety(cfg: Box<dyn Cfg>, block: Box<dyn Block>, tx: Box<dyn Tx>) {
        crate::test_utils::test_trevm().fill_cfg(&cfg).fill_block(&block).fill_tx(&tx);

        unimplemented!("compilation check only")
    }

    impl Block for () {
        fn fill_block_env(&self, block_env: &mut BlockEnv) {
            let BlockEnv {
                number,
                beneficiary,
                timestamp,
                gas_limit,
                basefee,
                difficulty,
                prevrandao,
                blob_excess_gas_and_price,
            } = block_env;
            *number = 1;
            *beneficiary = Default::default();
            *timestamp = 1720450148; // Time when I was writing the test code
            *gas_limit = 30_000_000;
            *basefee = 5 * GWEI_TO_WEI;

            let diff = B256::repeat_byte(0xab);
            *prevrandao = Some(diff);
            *difficulty = U256::from_be_bytes(diff.into());
            *blob_excess_gas_and_price = Some(BlobExcessGasAndPrice::new(1_000_000, false));
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
