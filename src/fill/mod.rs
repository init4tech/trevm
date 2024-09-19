mod alloy;

mod traits;
pub use traits::{Block, Cfg, Tx};

mod noop;
pub use noop::{NoopBlock, NoopCfg};

mod zenith;

use revm::primitives::{CfgEnv, TxEnv};

/// A [`Cfg`] that disables gas-related checks and payment of the
/// beneficiary reward, while leaving other cfg options unchanged.
///
/// ## Warning
///
/// This filler relies on the following optional features:
/// - `optional_balance_check`
/// - `optional_beneficiary_reward`
/// - `optional_gas_refund`
/// - `optional_no_base_fee`
///
///
/// It will disable the corresponding checks if the features are enabled. **If
/// none of the features are enabled, this filler will do nothing.**
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DisableGasChecks;

impl Cfg for DisableGasChecks {
    #[allow(unused_variables)]
    fn fill_cfg_env(&self, cfg_env: &mut CfgEnv) {
        #[cfg(feature = "optional_balance_check")]
        {
            cfg_env.disable_balance_check = true;
        }
        #[cfg(feature = "optional_beneficiary_reward")]
        {
            cfg_env.disable_beneficiary_reward = true;
        }
        #[cfg(feature = "optional_gas_refund")]
        {
            cfg_env.disable_gas_refund = true;
        }
        #[cfg(feature = "optional_no_base_fee")]
        {
            cfg_env.disable_base_fee = true;
        }
    }
}

/// A [`Tx`] that disables the nonce check, while leaving other [`TxEnv`]
/// attributes untouched.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DisableNonceCheck;

impl Tx for DisableNonceCheck {
    #[allow(unused_variables)]
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        tx_env.nonce = None;
    }
}
