use crate::Tx;
use alloy::primitives::{address, Address, Bytes, U256};
use revm::context::{TransactionType, TxEnv};

/// System smart contract calls as specified in [EIP-4788], [EIP-7002],
/// and [EIP-7251].
///
/// By default, these calls are sent from a special system caller address
/// specified in the EIPs, but this can be overridden using the
/// [`SystemTx::new_with_caller`] method.
///
/// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
/// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
/// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SystemTx {
    /// The target address of the system call.
    pub target: Address,
    /// The input data of the system call.
    pub input: Bytes,
    /// The caller address of the system call.
    pub caller: Address,
}

/// The system caller as specified in [EIP-4788], [EIP-7002], and [EIP-7251].
///
/// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
/// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
/// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
pub const DEFAULT_SYSTEM_CALLER: Address = address!("fffffffffffffffffffffffffffffffffffffffe");

impl SystemTx {
    /// Instantiate a new [`SystemTx`].
    pub const fn new(target: Address, input: Bytes) -> Self {
        Self { caller: DEFAULT_SYSTEM_CALLER, target, input }
    }

    /// Instantiate a new [`SystemTx`] with a custom caller address.
    pub const fn new_with_caller(target: Address, input: Bytes, caller: Address) -> Self {
        Self { caller, target, input }
    }
}

impl Tx for SystemTx {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        let TxEnv {
            tx_type,
            caller,
            gas_limit,
            gas_price,
            kind,
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

        *tx_type = TransactionType::Custom as u8;

        *caller = self.caller;
        *gas_limit = 30_000_000;
        // 0 gas price
        *gas_price = 0;
        *kind = self.target.into();
        *value = U256::ZERO;
        *data = self.input.clone();
        *nonce = 0;

        // disable chain id checks
        chain_id.take();
        // set priority fee to 0
        gas_priority_fee.take();
        // disable eip-2930
        access_list.0.clear();
        // disable eip-4844
        blob_hashes.clear();
        *max_fee_per_blob_gas = 0;
        // disable eip-7702
        authorization_list.clear();
    }
}
