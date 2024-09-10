use alloy_consensus::Signed;
use alloy_primitives::U256;
use revm::primitives::{BlobExcessGasAndPrice, BlockEnv, TxEnv};

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
            Self::Legacy(t) => t.fill_tx_env(tx_env),
            Self::Eip2930(t) => t.fill_tx_env(tx_env),
            Self::Eip1559(t) => t.fill_tx_env(tx_env),
            Self::Eip4844(t) => t.fill_tx_env(tx_env),
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

impl Block for alloy_rpc_types_eth::Header {
    fn fill_block_env(&self, block_env: &mut revm::primitives::BlockEnv) {
        let BlockEnv {
            number,
            coinbase,
            timestamp,
            gas_limit,
            basefee,
            difficulty,
            prevrandao,
            blob_excess_gas_and_price,
        } = block_env;
        *number = U256::from(self.number);
        *coinbase = self.miner;
        *timestamp = U256::from(self.timestamp);
        *gas_limit = U256::from(self.gas_limit);
        *basefee = U256::from(self.base_fee_per_gas.unwrap_or_default());
        *difficulty = U256::from(self.difficulty);
        *prevrandao = self.mix_hash;
        *blob_excess_gas_and_price =
            self.blob_gas_used.map(|ebg| BlobExcessGasAndPrice::new(ebg as u64));
    }
}

impl<T> Block for alloy_rpc_types_eth::Block<T> {
    fn fill_block_env(&self, block_env: &mut revm::primitives::BlockEnv) {
        self.header.fill_block_env(block_env);
    }

    fn tx_count_hint(&self) -> Option<usize> {
        Some(self.transactions.len())
    }
}

#[cfg(test)]
mod tests {
    use crate::{NoopBlock, NoopCfg, TrevmBuilder};
    use alloy_consensus::{Header, TxEnvelope, EMPTY_ROOT_HASH};

    use alloy_rlp::Decodable;

    use revm::{Evm, InMemoryDB};

    #[test]
    // Test vector from https://etherscan.io/tx/0xce4dc6d7a7549a98ee3b071b67e970879ff51b5b95d1c340bacd80fa1e1aab31
    fn test_live_tx_1559_fill() {
        let raw_tx = alloy_primitives::hex::decode("02f86f0102843b9aca0085029e7822d68298f094d9e1459a7a482635700cbc20bbaf52d495ab9c9680841b55ba3ac080a0c199674fcb29f353693dd779c017823b954b3c69dffa3cd6b2a6ff7888798039a028ca912de909e7e6cdef9cdcaf24c54dd8c1032946dfa1d85c206b32a9064fe8").unwrap();
        let tx = TxEnvelope::decode(&mut raw_tx.as_slice()).unwrap();

        let _ = Evm::builder()
            .with_db(InMemoryDB::default())
            .build_trevm()
            .fill_cfg(&NoopCfg)
            .fill_block(&NoopBlock)
            .fill_tx(&tx);
    }

    #[test]
    // Test vector from https://etherscan.io/tx/0x280cde7cdefe4b188750e76c888f13bd05ce9a4d7767730feefe8a0e50ca6fc4
    fn test_live_tx_legacy_fill() {
        let raw_tx = alloy_primitives::hex::decode("f9015482078b8505d21dba0083022ef1947a250d5630b4cf539739df2c5dacb4c659f2488d880c46549a521b13d8b8e47ff36ab50000000000000000000000000000000000000000000066ab5a608bd00a23f2fe000000000000000000000000000000000000000000000000000000000000008000000000000000000000000048c04ed5691981c42154c6167398f95e8f38a7ff00000000000000000000000000000000000000000000000000000000632ceac70000000000000000000000000000000000000000000000000000000000000002000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead9083c756cc20000000000000000000000006c6ee5e31d828de241282b9606c8e98ea48526e225a0c9077369501641a92ef7399ff81c21639ed4fd8fc69cb793cfa1dbfab342e10aa0615facb2f1bcf3274a354cfe384a38d0cc008a11c2dd23a69111bc6930ba27a8").unwrap();
        let tx = TxEnvelope::decode(&mut raw_tx.as_slice()).unwrap();

        let _ = Evm::builder()
            .with_db(InMemoryDB::default())
            .build_trevm()
            .fill_cfg(&NoopCfg)
            .fill_block(&NoopBlock)
            .fill_tx(&tx);
    }

    #[test]
    // Test vector from https://sepolia.etherscan.io/tx/0x9a22ccb0029bc8b0ddd073be1a1d923b7ae2b2ea52100bae0db4424f9107e9c0
    // Blobscan: https://sepolia.blobscan.com/tx/0x9a22ccb0029bc8b0ddd073be1a1d923b7ae2b2ea52100bae0db4424f9107e9c0
    fn test_live_tx_4844_fill() {
        let raw_tx = alloy_primitives::hex::decode("0x03f9011d83aa36a7820fa28477359400852e90edd0008252089411e9ca82a3a762b4b5bd264d4173a242e7a770648080c08504a817c800f8a5a0012ec3d6f66766bedb002a190126b3549fce0047de0d4c25cffce0dc1c57921aa00152d8e24762ff22b1cfd9f8c0683786a7ca63ba49973818b3d1e9512cd2cec4a0013b98c6c83e066d5b14af2b85199e3d4fc7d1e778dd53130d180f5077e2d1c7a001148b495d6e859114e670ca54fb6e2657f0cbae5b08063605093a4b3dc9f8f1a0011ac212f13c5dff2b2c6b600a79635103d6f580a4221079951181b25c7e654901a0c8de4cced43169f9aa3d36506363b2d2c44f6c49fc1fd91ea114c86f3757077ea01e11fdd0d1934eda0492606ee0bb80a7bf8f35cc5f86ec60fe5031ba48bfd544").unwrap();
        let tx = TxEnvelope::decode(&mut raw_tx.as_slice()).unwrap();

        let _ = Evm::builder()
            .with_db(InMemoryDB::default())
            .build_trevm()
            .fill_cfg(&NoopCfg)
            .fill_block(&NoopBlock)
            .fill_tx(&tx);
    }

    #[test]
    fn test_header_fill() {
        let raw = r#"{"parentHash":"0x0000000000000000000000000000000000000000000000000000000000000000","ommersHash":"0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347","beneficiary":"0x0000000000000000000000000000000000000000","stateRoot":"0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421","transactionsRoot":"0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421","receiptsRoot":"0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421","withdrawalsRoot":"0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421","logsBloom":"0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000","difficulty":"0x0","number":"0x0","gasLimit":"0x0","gasUsed":"0x0","timestamp":"0x0","mixHash":"0x0000000000000000000000000000000000000000000000000000000000000000","nonce":"0x0000000000000000","baseFeePerGas":"0x1","extraData":"0x"}"#;
        let header = Header {
            base_fee_per_gas: Some(1),
            withdrawals_root: Some(EMPTY_ROOT_HASH),
            ..Default::default()
        };

        let json = serde_json::to_string(&header).unwrap();
        assert_eq!(json, raw);

        // Fill using the constructed header
        let _ = Evm::builder()
            .with_db(InMemoryDB::default())
            .build_trevm()
            .fill_cfg(&NoopCfg)
            .fill_block(&header);
    }
}
