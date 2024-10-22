use super::{checked_insert_code, execute_system_tx};
use crate::{system::SystemTx, EvmNeedsTx};
use alloy::eips::eip7251::CONSOLIDATION_REQUEST_PREDEPLOY_CODE;
use alloy_primitives::{Address, Bytes};
use revm::{
    primitives::{EVMError, SpecId},
    Database, DatabaseCommit,
};

/// The address for the [EIP-7251] consolidation requests contract
///
/// [`EIP-7251`]: https://eips.ethereum.org/EIPS/eip-7251
pub use alloy::eips::eip7251::CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS;

/// The size of a consolidation request in bytes.
pub const CONSOLIDATION_REQUEST_BYTES: usize = 20 + 48 + 48;

impl SystemTx {
    /// Instantiate a system call for the post-block consolidation requests as
    /// specified in [EIP-7251].
    ///
    /// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
    pub const fn eip7251() -> Self {
        Self::eip7251_with_target(CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS)
    }

    /// Instantiate a system call for the post-block consolidation requests as
    /// specified in [EIP-7251], with a custom target address.
    ///
    /// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
    pub const fn eip7251_with_target(target: Address) -> Self {
        Self::new(target, Bytes::new())
    }

    /// Instantiate a system call for the post-block consolidation requests as
    /// specified in [EIP-7251], with a custom target address and caller
    /// address.
    ///
    /// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
    pub const fn eip7251_with_target_and_caller(target: Address, caller: Address) -> Self {
        Self::new_with_caller(target, Bytes::new(), caller)
    }
}

impl<'a, Ext, Db: Database + DatabaseCommit> EvmNeedsTx<'a, Ext, Db> {
    /// Apply a system transaction as specified in [EIP-7251]. The EIP-7251
    /// post-block action calls the consolidation request contract to process
    /// consolidation requests.
    ///
    /// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
    pub fn apply_eip7251(&mut self) -> Result<Bytes, EVMError<Db::Error>>
    where
        Db: Database + DatabaseCommit,
    {
        if self.spec_id() < SpecId::PRAGUE {
            return Ok(Bytes::new());
        }

        checked_insert_code(
            self.inner_mut_unchecked(),
            CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS,
            &CONSOLIDATION_REQUEST_PREDEPLOY_CODE,
        )?;

        let res = execute_system_tx(self.inner_mut_unchecked(), &SystemTx::eip7251())?;

        // We make assumptions here:
        // - The system transaction never reverts.
        // - The system transaction always has an output.
        // - The system contract produces correct output.
        // - The output is a list of consolidation requests.
        // - The output does not contain incomplete requests.

        let Some(output) = res.output() else {
            panic!("execution halted during consolidation request system contract execution")
        };

        Ok(output.clone())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use alloy::consensus::constants::ETH_TO_WEI;
    use alloy_primitives::{fixed_bytes, FixedBytes, TxKind, U256};

    use crate::{NoopBlock, NoopCfg, Tx};

    const WITHDRAWAL_ADDR: Address = Address::with_last_byte(0x42);
    const VALIDATOR_PUBKEY: FixedBytes<48> = fixed_bytes!("111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111");
    const TARGET_VALIDATOR_PUBKEY: FixedBytes<48> = fixed_bytes!("111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111");

    struct ConsolidationTx;

    impl Tx for ConsolidationTx {
        fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
            let input: Bytes =
                [&VALIDATOR_PUBKEY[..], &TARGET_VALIDATOR_PUBKEY[..]].concat().into();

            tx_env.caller = WITHDRAWAL_ADDR;
            tx_env.data = input;
            tx_env.transact_to = TxKind::Call(CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS);
            // `MIN_CONSOLIDATION_REQUEST_FEE`
            tx_env.value = U256::from(1);
        }
    }

    #[test]
    fn test_eip7251() {
        let mut trevm = crate::test_utils::test_trevm().fill_cfg(&NoopCfg).fill_block(&NoopBlock);

        // insert the code
        trevm.apply_eip7251().unwrap();

        trevm.test_increase_balance(WITHDRAWAL_ADDR, U256::from(100 * ETH_TO_WEI));

        let mut trevm = trevm.run_tx(&ConsolidationTx).unwrap().accept_state();

        let requests = trevm.apply_eip7251().unwrap();

        assert_eq!(&requests[..20], WITHDRAWAL_ADDR.as_slice());
        assert_eq!(&requests[20..68], VALIDATOR_PUBKEY.as_slice());
        assert_eq!(&requests[68..], TARGET_VALIDATOR_PUBKEY.as_slice());
    }
}
