use alloy::{
    consensus::{proofs::ordered_trie_root_with_encoder, ReceiptEnvelope, TxReceipt},
    eips::eip2718::Encodable2718,
    primitives::{Address, Bloom, Bytes, Log, B256},
};
use std::sync::OnceLock;

/// Information externalized during block execution.
///
/// This struct is used to collect the results of executing a block of
/// transactions. It accumulates the receipts and senders of the transactions.
#[derive(Debug, Clone)]
pub struct BlockOutput<T: TxReceipt = ReceiptEnvelope> {
    /// The receipts of the transactions in the block, in order.
    receipts: Vec<T>,

    /// The senders of the transactions in the block, in order.
    senders: Vec<Address>,

    /// The logs bloom of the block.
    bloom: OnceLock<Bloom>,

    /// The receipt root of the block.
    receipt_root: OnceLock<B256>,
}

impl Default for BlockOutput {
    fn default() -> Self {
        Self::with_capacity(0)
    }
}

impl<T: TxReceipt<Log = alloy::primitives::Log>> BlockOutput<T> {
    /// Create a new block output with memory allocated to hold `capacity`
    /// transaction outcomes.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            receipts: Vec::with_capacity(capacity),
            senders: Vec::with_capacity(capacity),
            bloom: Default::default(),
            receipt_root: Default::default(),
        }
    }

    fn seal_bloom(&self) {
        self.bloom.get_or_init(|| {
            self.receipts.iter().fold(Bloom::default(), |mut bloom, r| {
                bloom |= r.bloom();
                bloom
            })
        });
    }

    fn unseal(&mut self) {
        self.bloom.take();
        self.receipt_root.take();
    }

    /// Reserve memory for `capacity` transaction outcomes.
    pub fn reserve(&mut self, capacity: usize) {
        self.receipts.reserve(capacity);
        self.senders.reserve(capacity);
    }

    /// Get a reference to the receipts of the transactions in the block.
    #[allow(clippy::missing_const_for_fn)] // false positive
    pub fn receipts(&self) -> &[T] {
        &self.receipts
    }

    /// Get an iterator over the logs of the transactions in the block.
    pub fn logs(&self) -> impl Iterator<Item = &Log> {
        self.receipts.iter().flat_map(|r| r.logs())
    }

    /// Get the logs bloom of the block.
    pub fn logs_bloom(&self) -> Bloom {
        self.seal_bloom();
        *self.bloom.get().unwrap()
    }

    /// Get a reference the senders of the transactions in the block.
    #[allow(clippy::missing_const_for_fn)] // false positive
    pub fn senders(&self) -> &[Address] {
        &self.senders
    }

    /// Get the cumulative gas used in the block.
    pub fn cumulative_gas_used(&self) -> u64 {
        self.receipts().last().map(TxReceipt::cumulative_gas_used).unwrap_or_default()
    }

    /// Accumulate the result of a transaction execution. If `parse_deposits` is
    /// true, the logs of the transaction will be scanned for deposit events
    /// according to the [EIP-6110] specification.
    ///
    /// [EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110
    pub fn push_result(&mut self, receipt: T, sender: Address) {
        self.unseal();
        self.push_receipt(receipt);
        self.push_sender(sender);
    }

    /// Push a receipt onto the list of receipts.
    fn push_receipt(&mut self, receipt: T) {
        self.receipts.push(receipt);
    }

    /// Push a sender onto the list of senders.
    fn push_sender(&mut self, sender: Address) {
        self.senders.push(sender);
    }

    /// Find deposits in the logs of the transactions in the block.
    pub fn find_deposit_requests(&self) -> impl Iterator<Item = Bytes> + use<'_, T> {
        crate::system::eip6110::check_logs_for_deposits(
            self.receipts().iter().flat_map(TxReceipt::logs),
        )
    }

    /// Deconstruct the block output into its parts, returning any memoized
    /// bloom and receipt root values.
    pub fn into_parts(self) -> (Vec<T>, Vec<Address>, Option<Bloom>, Option<B256>) {
        (self.receipts, self.senders, self.bloom.into_inner(), self.receipt_root.into_inner())
    }
}

impl<T: TxReceipt + Encodable2718> BlockOutput<T> {
    /// Seal the block output, computing and memoizing the logs bloom and
    /// receipt root in a single pass over the receipts. The block bloom is
    /// derived as a side effect of receipt root computation by accumulating
    /// per-receipt blooms during trie encoding.
    ///
    /// Subsequent calls to [`logs_bloom`] and [`receipt_root`] will return
    /// the memoized values without recomputation.
    ///
    /// [`logs_bloom`]: Self::logs_bloom
    /// [`receipt_root`]: Self::receipt_root
    pub fn seal(&self) {
        if self.bloom.get().is_some() && self.receipt_root.get().is_some() {
            return;
        }

        let mut block_bloom = Bloom::default();
        let root = ordered_trie_root_with_encoder(&self.receipts, |r, buf| {
            block_bloom |= r.bloom();
            r.encode_2718(buf);
        });

        self.bloom.get_or_init(|| block_bloom);
        self.receipt_root.get_or_init(|| root);
    }

    /// Get the receipt root of the block.
    pub fn receipt_root(&self) -> B256 {
        self.seal();
        *self.receipt_root.get().unwrap()
    }

    /// Seal and deconstruct the block output into its parts.
    pub fn into_sealed_parts(self) -> (Vec<T>, Vec<Address>, Bloom, B256) {
        self.seal();
        (
            self.receipts,
            self.senders,
            self.bloom.into_inner().expect("seal sets bloom"),
            self.receipt_root.into_inner().expect("seal sets receipt_root"),
        )
    }
}

impl<T: TxReceipt + PartialEq> PartialEq for BlockOutput<T> {
    fn eq(&self, other: &Self) -> bool {
        self.receipts == other.receipts && self.senders == other.senders
    }
}

impl<T: TxReceipt + Eq> Eq for BlockOutput<T> {}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy::{
        consensus::{
            constants::EMPTY_ROOT_HASH, Receipt, ReceiptEnvelope, ReceiptWithBloom, TxType,
        },
        primitives::{b256, Address, Bloom},
    };

    fn envelope(tx_type: TxType, receipt: ReceiptWithBloom<Receipt>) -> ReceiptEnvelope {
        ReceiptEnvelope::from_typed(tx_type, receipt)
    }

    #[test]
    fn block_output_eq_with_one_populated_bloom() {
        let output_a = BlockOutput::default();
        let output_b = BlockOutput::default();
        output_a.logs_bloom();
        assert!(output_a.bloom.get().is_some());
        assert!(output_b.bloom.get().is_none());
        assert_eq!(output_a, output_b);
    }

    #[test]
    fn empty_receipt_root() {
        let output = BlockOutput::default();
        assert_eq!(output.receipt_root(), EMPTY_ROOT_HASH);
        assert_eq!(output.logs_bloom(), Bloom::ZERO);
    }

    #[test]
    fn seal_computes_bloom_and_root() {
        let output = BlockOutput::default();
        assert!(output.bloom.get().is_none());
        assert!(output.receipt_root.get().is_none());

        output.seal();

        assert!(output.bloom.get().is_some());
        assert!(output.receipt_root.get().is_some());
    }

    #[test]
    fn single_eip2930_receipt_root() {
        // Test vector from:
        // - https://github.com/alloy-rs/alloy/blob/main/crates/consensus/src/receipt/mod.rs (check_receipt_root_optimism)
        // - https://github.com/paradigmxyz/reth/blob/main/crates/ethereum/primitives/src/receipt.rs (check_receipt_root_optimism)
        let logs = vec![Log::new_unchecked(Address::ZERO, vec![], Default::default())];
        let bloom = Bloom::from(alloy::primitives::hex!(
            "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"
        ));

        let receipt = ReceiptWithBloom {
            receipt: Receipt {
                status: alloy::consensus::Eip658Value::success(),
                cumulative_gas_used: 102068,
                logs,
            },
            logs_bloom: bloom,
        };

        let mut output = BlockOutput::default();
        output.push_result(envelope(TxType::Eip2930, receipt), Address::ZERO);

        assert_eq!(
            output.receipt_root(),
            b256!("0xfe70ae4a136d98944951b2123859698d59ad251a381abc9960fa81cae3d0d4a0"),
        );
        assert_eq!(output.logs_bloom(), bloom);
    }

    #[test]
    fn mixed_receipt_types() {
        // Adapted from https://github.com/paradigmxyz/reth/blob/main/crates/engine/tree/src/tree/payload_processor/receipt_root_task.rs
        // (test_receipt_root_matches_standard_calculation)
        let default_receipt = || ReceiptWithBloom {
            receipt: Receipt {
                status: alloy::consensus::Eip658Value::success(),
                cumulative_gas_used: 0,
                logs: vec![],
            },
            logs_bloom: Bloom::ZERO,
        };

        let legacy = {
            let mut r = default_receipt();
            r.receipt.cumulative_gas_used = 21000;
            envelope(TxType::Legacy, r)
        };
        let eip1559 = {
            let mut r = default_receipt();
            r.receipt.cumulative_gas_used = 42000;
            r.receipt.logs =
                vec![Log::new_unchecked(Address::ZERO, vec![B256::ZERO], Bytes::new())];
            r.logs_bloom = alloy::consensus::TxReceipt::bloom(&r.receipt);
            envelope(TxType::Eip1559, r)
        };
        let eip2930 = {
            let mut r = default_receipt();
            r.receipt.cumulative_gas_used = 63000;
            r.receipt.status = alloy::consensus::Eip658Value::Eip658(false);
            envelope(TxType::Eip2930, r)
        };

        let mut output = BlockOutput::default();
        output.push_result(legacy, Address::ZERO);
        output.push_result(eip1559, Address::ZERO);
        output.push_result(eip2930, Address::ZERO);

        assert_eq!(
            output.receipt_root(),
            b256!("0xa4746a21d06f407a22200fed3491774c1b455736af092b7dcd7565de6b11da0c"),
        );
        assert_eq!(
            output.logs_bloom(),
            Bloom::from(alloy::primitives::hex!(
                "00000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000800000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000"
            )),
        );
    }

    #[test]
    fn into_sealed_parts_returns_all() {
        let receipt = ReceiptWithBloom {
            receipt: Receipt {
                status: alloy::consensus::Eip658Value::success(),
                cumulative_gas_used: 100,
                logs: vec![],
            },
            logs_bloom: Bloom::ZERO,
        };

        let mut output = BlockOutput::default();
        output.push_result(envelope(TxType::Legacy, receipt), Address::ZERO);

        let (receipts, senders, bloom, root) = output.into_sealed_parts();
        assert_eq!(receipts.len(), 1);
        assert_eq!(senders.len(), 1);
        assert_eq!(
            root,
            b256!("0x134447aac1b9bfa029f21da1cad6d6a71f841f16dc45134b24f14effe1efe791"),
        );
        assert_eq!(bloom, Bloom::ZERO);
    }

    #[test]
    fn into_parts_without_seal() {
        let mut output = BlockOutput::default();
        output.push_result(
            envelope(
                TxType::Legacy,
                ReceiptWithBloom {
                    receipt: Receipt {
                        status: alloy::consensus::Eip658Value::success(),
                        cumulative_gas_used: 100,
                        logs: vec![],
                    },
                    logs_bloom: Bloom::ZERO,
                },
            ),
            Address::ZERO,
        );

        let (receipts, senders, bloom, root) = output.into_parts();
        assert_eq!(receipts.len(), 1);
        assert_eq!(senders.len(), 1);
        assert!(bloom.is_none());
        assert!(root.is_none());
    }

    #[test]
    fn unseal_clears_memoized_values() {
        let mut output = BlockOutput::default();
        output.seal();
        assert!(output.bloom.get().is_some());
        assert!(output.receipt_root.get().is_some());

        output.push_result(
            envelope(
                TxType::Legacy,
                ReceiptWithBloom {
                    receipt: Receipt {
                        status: alloy::consensus::Eip658Value::success(),
                        cumulative_gas_used: 100,
                        logs: vec![],
                    },
                    logs_bloom: Bloom::ZERO,
                },
            ),
            Address::ZERO,
        );

        // push_result calls unseal
        assert!(output.bloom.get().is_none());
        assert!(output.receipt_root.get().is_none());
    }
}
