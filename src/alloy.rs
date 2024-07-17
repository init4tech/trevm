use alloy_consensus::Signed;
use alloy_primitives::U256;
use revm::primitives::{BlockEnv, TxEnv};

use crate::{Block, Tx};

impl Tx for Signed<alloy_consensus::TxLegacy> {
    fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
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
        *caller = self.recover_signer().unwrap();
        *gas_limit = self.tx().gas_limit as u64;
        *gas_price = U256::from(self.tx().gas_price);
        *transact_to = self.tx().to;
        *value = self.tx().value;
        *data = self.tx().input.clone();
        *nonce = Some(self.tx().nonce);
        *chain_id = self.tx().chain_id;
        access_list.clear();
        gas_priority_fee.take();
        blob_hashes.clear();
        max_fee_per_blob_gas.take();
        authorization_list.take();
    }
}

impl Tx for Signed<alloy_consensus::TxEip2930> {
    fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
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
        *caller = self.recover_signer().unwrap();
        *gas_limit = self.tx().gas_limit as u64;
        *gas_price = U256::from(self.tx().gas_price);
        *transact_to = self.tx().to;
        *value = self.tx().value;
        *data = self.tx().input.clone();
        *nonce = Some(self.tx().nonce);
        *chain_id = Some(self.tx().chain_id);
        access_list.clone_from(&self.tx().access_list.0);
        gas_priority_fee.take();
        blob_hashes.clear();
        max_fee_per_blob_gas.take();
        authorization_list.take();
    }
}

impl Tx for Signed<alloy_consensus::TxEip1559> {
    fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
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
        *caller = self.recover_signer().unwrap();
        *gas_limit = self.tx().gas_limit as u64;
        *gas_price = U256::from(self.tx().max_fee_per_gas);
        *transact_to = self.tx().to;
        *value = self.tx().value;
        *data = self.tx().input.clone();
        *nonce = Some(self.tx().nonce);
        *chain_id = Some(self.tx().chain_id);
        access_list.clone_from(&self.tx().access_list.0);
        *gas_priority_fee = Some(U256::from(self.tx().max_priority_fee_per_gas));
        blob_hashes.clear();
        max_fee_per_blob_gas.take();
        authorization_list.take();
    }
}

impl Tx for Signed<alloy_consensus::TxEip4844> {
    fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
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
        *caller = self.recover_signer().unwrap();
        *gas_limit = self.tx().gas_limit as u64;
        *gas_price = U256::from(self.tx().max_fee_per_gas);
        *transact_to = self.tx().to.into();
        *value = self.tx().value;
        *data = self.tx().input.clone();
        *nonce = Some(self.tx().nonce);
        *chain_id = Some(self.tx().chain_id);
        access_list.clone_from(&self.tx().access_list.0);
        *gas_priority_fee = Some(U256::from(self.tx().max_priority_fee_per_gas));
        blob_hashes.clone_from(&self.tx().blob_versioned_hashes);
        *max_fee_per_blob_gas = Some(U256::from(self.tx().max_fee_per_blob_gas));
        authorization_list.take();
    }
}

impl Tx for Signed<alloy_consensus::TxEip4844WithSidecar> {
    fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
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
        *caller = self.recover_signer().unwrap();
        *gas_limit = self.tx().tx.gas_limit as u64;
        *gas_price = U256::from(self.tx().tx.max_fee_per_gas);
        *transact_to = self.tx().tx.to.into();
        *value = self.tx().tx.value;
        *data = self.tx().tx.input.clone();
        *nonce = Some(self.tx().tx.nonce);
        *chain_id = Some(self.tx().tx.chain_id);
        access_list.clone_from(&self.tx().tx.access_list.0);
        *gas_priority_fee = Some(U256::from(self.tx().tx.max_priority_fee_per_gas));
        blob_hashes.clone_from(&self.tx().tx.blob_versioned_hashes);
        *max_fee_per_blob_gas = Some(U256::from(self.tx().tx.max_fee_per_blob_gas));
        authorization_list.take();
    }
}

impl Tx for Signed<alloy_consensus::TxEip4844Variant> {
    fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
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
        let tx = match self.tx() {
            alloy_consensus::TxEip4844Variant::TxEip4844(tx) => tx,
            alloy_consensus::TxEip4844Variant::TxEip4844WithSidecar(tx) => &tx.tx,
        };
        *caller = self.recover_signer().unwrap();
        *gas_limit = tx.gas_limit as u64;
        *gas_price = U256::from(tx.max_fee_per_gas);
        *transact_to = tx.to.into();
        *value = tx.value;
        *data = tx.input.clone();
        *nonce = Some(tx.nonce);
        *chain_id = Some(tx.chain_id);
        access_list.clone_from(&tx.access_list.0);
        *gas_priority_fee = Some(U256::from(tx.max_priority_fee_per_gas));
        blob_hashes.clone_from(&tx.blob_versioned_hashes);
        *max_fee_per_blob_gas = Some(U256::from(tx.max_fee_per_blob_gas));
        authorization_list.take();
    }
}

impl Tx for alloy_consensus::TxEnvelope {
    fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
        match self {
            alloy_consensus::TxEnvelope::Legacy(t) => t.fill_tx_env(tx_env),
            alloy_consensus::TxEnvelope::Eip2930(t) => t.fill_tx_env(tx_env),
            alloy_consensus::TxEnvelope::Eip1559(t) => t.fill_tx_env(tx_env),
            alloy_consensus::TxEnvelope::Eip4844(t) => t.fill_tx_env(tx_env),
            _ => panic!("Unsupported transaction type"),
        }
    }
}

impl Block for alloy_consensus::Header {
    fn fill_block_env(&self, block_env: &mut revm::primitives::BlockEnv) {
        let BlockEnv {
            number,
            coinbase,
            timestamp,
            gas_limit,
            basefee,
            difficulty,
            prevrandao,
            blob_excess_gas_and_price: _,
        } = block_env;
        *number = U256::from(self.number);
        *coinbase = self.beneficiary;
        *timestamp = U256::from(self.timestamp);
        *gas_limit = U256::from(self.gas_limit);
        *basefee = self.base_fee_per_gas.map_or_else(Default::default, U256::from);

        *difficulty = self.difficulty;
        *prevrandao = if self.difficulty.is_zero() { Some(self.mix_hash) } else { None };

        if let Some(excess_blob_gas) = self.excess_blob_gas {
            block_env.set_blob_excess_gas_and_price(excess_blob_gas as u64);
        }
    }

    fn tx_count_hint(&self) -> Option<usize> {
        None
    }
}
