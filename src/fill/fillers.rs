use crate::fill::traits::{Cfg, Tx};
use revm::context::{BlockEnv, CfgEnv, TxEnv};

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
        #[cfg(feature = "optional_no_base_fee")]
        {
            cfg_env.disable_base_fee = true;
        }
    }
}

/// A [`Cfg`] that disables the nonce check, while leaving other [`CfgEnv`]
/// attributes untouched.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DisableNonceCheck;

impl Cfg for DisableNonceCheck {
    #[allow(unused_variables)]
    fn fill_cfg_env(&self, cfg_env: &mut CfgEnv) {
        cfg_env.disable_nonce_check = true;
    }
}

/// Prime the EVM for gas estimation. This filler is all of [`Cfg`], and
/// [`Tx`]. It is used internally by [`crate::Trevm::estimate_gas`], and is
/// considered a low-level API. Generally it is not correct to import this
/// type.
#[cfg(feature = "estimate_gas")]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct GasEstimationFiller {
    pub(crate) gas_limit: u64,
}

#[cfg(feature = "estimate_gas")]
impl From<u64> for GasEstimationFiller {
    fn from(gas_limit: u64) -> Self {
        Self { gas_limit }
    }
}

#[cfg(feature = "estimate_gas")]
impl Cfg for GasEstimationFiller {
    fn fill_cfg_env(&self, cfg_env: &mut CfgEnv) {
        cfg_env.disable_base_fee = true;
        cfg_env.disable_eip3607 = true;
        DisableNonceCheck.fill_cfg_env(cfg_env);
    }
}

#[cfg(feature = "estimate_gas")]
impl Tx for GasEstimationFiller {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        tx_env.gas_limit = self.gas_limit;
    }
}

#[cfg(feature = "call")]
pub(crate) struct CallFiller {
    pub gas_limit: u64,
}

#[cfg(feature = "call")]
impl Cfg for CallFiller {
    fn fill_cfg_env(&self, cfg_env: &mut CfgEnv) {
        cfg_env.disable_base_fee = true;
        cfg_env.disable_eip3607 = true;
        DisableNonceCheck.fill_cfg_env(cfg_env);
    }
}

#[cfg(feature = "call")]
impl crate::Block for CallFiller {
    fn fill_block_env(&self, block_env: &mut BlockEnv) {
        block_env.gas_limit = self.gas_limit;
    }
}
