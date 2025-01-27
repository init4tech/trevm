use crate::{Block, Tx};
use alloy::primitives::{Address, U256};
use alloy_sol_types::SolCall;
use revm::primitives::{TransactTo, TxEnv};
use zenith_types::{Passage::EnterToken, Transactor, ZenithCallBundle};

impl Tx for Transactor::Transact {
    fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
        // destructuring here means that any changes to the fields will result
        // in breaking changes here, ensuring that they never silently add new
        // fields
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

        *caller = self.sender;
        *gas_limit = self.gas.as_limbs()[0];
        *gas_price = self.maxFeePerGas;
        *gas_priority_fee = Some(U256::ZERO);
        *transact_to = TransactTo::Call(self.to);
        *value = self.value;
        *data = self.data.clone();
        *chain_id = Some(self.rollup_chain_id());
        // This causes nonce validation to be skipped. i.e. the Transact event
        // will always use the next available nonce
        *nonce = None;
        *access_list = vec![];
        blob_hashes.clear();
        max_fee_per_blob_gas.take();
        authorization_list.take();
    }
}

impl Tx for EnterToken {
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

        *caller = zenith_types::MINTER_ADDRESS;
        *gas_limit = 1_000_000;
        *gas_price = U256::ZERO;
        // This is deliberately not set, as it is not known by the event.
        *transact_to = Address::ZERO.into();
        *value = U256::ZERO;
        *data = zenith_types::mintCall { amount: self.amount(), to: self.rollupRecipient }
            .abi_encode()
            .into();
        *nonce = None;
        *chain_id = Some(self.rollup_chain_id());
        *access_list = vec![];
        *gas_priority_fee = Some(U256::ZERO);
        blob_hashes.clear();
        max_fee_per_blob_gas.take();
        authorization_list.take();
    }
}

impl Block for ZenithCallBundle {
    fn fill_block_env(&self, block_env: &mut revm::primitives::BlockEnv) {
        block_env.number =
            self.bundle.state_block_number.as_number().map(U256::from).unwrap_or(block_env.number);
        block_env.timestamp = self.bundle.timestamp.map(U256::from).unwrap_or(block_env.timestamp);
        block_env.gas_limit = self.bundle.gas_limit.map(U256::from).unwrap_or(block_env.gas_limit);
        block_env.difficulty =
            self.bundle.difficulty.map(U256::from).unwrap_or(block_env.difficulty);
        block_env.basefee = self.bundle.base_fee.map(U256::from).unwrap_or(block_env.basefee);
    }
}
