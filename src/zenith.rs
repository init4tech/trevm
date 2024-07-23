use crate::Tx;
use alloy_primitives::U256;
use revm::primitives::{TransactTo, TxEnv};
use zenith_types::Transactor;

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
