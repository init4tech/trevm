use crate::Tx;
use alloy_primitives::{address, Address, Bytes, U256};
use revm::primitives::TxEnv;

/// System smart contract calls as specified in [EIP-4788], [EIP-7002],
/// and [EIP-7251].
///
/// These calls are sent from a special system caller address.
///
/// [`EIP-4788`]: https://eips.ethereum.org/EIPS/eip-4788
/// [`EIP-7002`]: https://eips.ethereum.org/EIPS/eip-7002
/// [`EIP-7251`]: https://eips.ethereum.org/EIPS/eip-7251
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SystemCall {
    /// The caller address of the system call.
    pub caller: Address,
    /// The target address of the system call.
    pub target: Address,
    /// The input data of the system call.
    pub input: Bytes,
}

/// The system caller as specified in [EIP-4788], [EIP-7002], and [EIP-7251].
///
/// [`EIP-4788`]: https://eips.ethereum.org/EIPS/eip-4788
/// [`EIP-7002`]: https://eips.ethereum.org/EIPS/eip-7002
/// [`EIP-7251`]: https://eips.ethereum.org/EIPS/eip-7251
pub const DEFAULT_SYSTEM_CALLER: Address = address!("fffffffffffffffffffffffffffffffffffffffe");

impl SystemCall {
    /// Instantiate a new [`SystemCall`].
    pub const fn new(target: Address, input: Bytes) -> Self {
        Self { caller: DEFAULT_SYSTEM_CALLER, target, input }
    }

    /// Instantiate a new [`SystemCall`] with a custom caller address.
    pub const fn new_with_caller(caller: Address, target: Address, input: Bytes) -> Self {
        Self { caller, target, input }
    }
}

impl Tx for SystemCall {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        let TxEnv {
            caller,
            gas_limit,
            gas_price,
            transact_to,
            value,
            data,
            nonce,
            chain_id,
            access_list,
            gas_priority_fee,
            blob_hashes,
            max_fee_per_blob_gas,
            authorization_list,
        } = tx_env;
        *caller = self.caller;
        *gas_limit = 30_000_000;
        *gas_price = U256::ZERO;
        *transact_to = self.target.into();
        *value = U256::ZERO;
        *data = self.input.clone();
        nonce.take();
        chain_id.take();
        gas_priority_fee.take();
        access_list.clear();
        blob_hashes.clear();
        max_fee_per_blob_gas.take();
        authorization_list.take();
    }
}
