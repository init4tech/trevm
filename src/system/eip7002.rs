use super::{checked_insert_code, execute_system_tx};
use crate::{system::SystemTx, EvmNeedsTx};
use alloy::eips::eip7002::WITHDRAWAL_REQUEST_PREDEPLOY_CODE;
use alloy::primitives::{Address, Bytes};
use revm::{context::result::EVMError, primitives::hardfork::SpecId, Database, DatabaseCommit};

/// The address for the [EIP-7002] withdrawal requests contract.
///
/// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
pub use alloy::eips::eip7002::WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS;

/// The size of a withdrawal request in bytes.
pub const WITHDRAWAL_REQUEST_BYTES: usize = 20 + 48 + 8;

impl SystemTx {
    /// Instantiate a system call for the post-block withdrawal requests as
    /// specified in [EIP-7002].
    ///
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    pub const fn eip7002() -> Self {
        Self::eip7002_with_target(WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS)
    }

    /// Instantiate a system call for the post-block withdrawal requests as
    /// specified in [EIP-7002], with a custom target address.
    ///
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    pub const fn eip7002_with_target(target: Address) -> Self {
        Self::new(target, Bytes::new())
    }

    /// Instantiate a system call for the post-block withdrawal requests as
    /// specified in [EIP-7002], with a custom target address and caller
    /// address.
    ///
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    pub const fn eip7002_with_target_and_caller(target: Address, caller: Address) -> Self {
        Self::new_with_caller(target, Bytes::new(), caller)
    }
}

impl<Ext, Db: Database + DatabaseCommit> EvmNeedsTx<Ext, Db> {
    /// Apply a system transaction as specified in [EIP-7002]. The EIP-7002
    /// post-block action was introduced in Prague, and calls the withdrawal
    /// request contract to accumulate withdrawal requests.
    ///
    /// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
    pub fn apply_eip7002(&mut self) -> Result<Bytes, EVMError<Db::Error>>
    where
        Db: Database + DatabaseCommit,
    {
        if self.spec_id() < SpecId::PRAGUE {
            return Ok(Bytes::new());
        }

        checked_insert_code(
            self.inner_mut_unchecked(),
            WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS,
            &WITHDRAWAL_REQUEST_PREDEPLOY_CODE,
        )?;

        let res = execute_system_tx(self.inner_mut_unchecked(), &SystemTx::eip7002())?;

        // We make assumptions here:
        // - The system transaction never reverts.
        // - The system transaction always has an output.
        // - The system contract produces correct output.
        // - The output is a list of withdrawal requests.
        // - The output does not contain incomplete requests.

        let Some(output) = res.output() else {
            panic!("execution halted during withdrawal request system contract execution")
        };

        Ok(output.clone())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use alloy::{
        consensus::constants::ETH_TO_WEI,
        primitives::{fixed_bytes, FixedBytes, TxKind, U256},
    };
    use revm::context::TxEnv;

    use crate::{NoopBlock, NoopCfg, Tx};

    const WITHDRAWAL_ADDR: Address = Address::with_last_byte(0x42);
    const WITHDRAWAL_AMOUNT: FixedBytes<8> = fixed_bytes!("2222222222222222");
    const VALIDATOR_PUBKEY: FixedBytes<48> = fixed_bytes!("111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111");

    struct WithdrawalTx;

    impl Tx for WithdrawalTx {
        fn fill_tx_env(&self, tx_env: &mut TxEnv) {
            // https://github.com/lightclient/7002asm/blob/e0d68e04d15f25057af7b6d180423d94b6b3bdb3/test/Contract.t.sol.in#L49-L64
            let input: Bytes = [&VALIDATOR_PUBKEY[..], &WITHDRAWAL_AMOUNT[..]].concat().into();

            tx_env.caller = WITHDRAWAL_ADDR;
            tx_env.data = input;
            tx_env.transact_to = TxKind::Call(WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS);
            // `MIN_WITHDRAWAL_REQUEST_FEE`
            tx_env.value = U256::from(1);
        }
    }

    #[test]
    fn test_eip7002() {
        let mut trevm = crate::test_utils::test_trevm().fill_cfg(&NoopCfg).fill_block(&NoopBlock);

        // insert the code
        trevm.apply_eip7002().unwrap();

        trevm.test_increase_balance(WITHDRAWAL_ADDR, U256::from(100 * ETH_TO_WEI));

        let mut trevm = trevm.run_tx(&WithdrawalTx).unwrap().accept_state();

        let requests = trevm.apply_eip7002().unwrap();

        assert_eq!(requests.len(), WITHDRAWAL_REQUEST_BYTES);

        assert_eq!(&requests[0..20], WITHDRAWAL_ADDR.as_slice());
        assert_eq!(&requests[20..68], VALIDATOR_PUBKEY.as_slice());
        assert_eq!(&requests[68..], WITHDRAWAL_AMOUNT.as_slice());
    }
}
