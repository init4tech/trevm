use alloc::vec::Vec;
use alloy::{
    consensus::{ReceiptEnvelope, TxReceipt},
    eips::eip6110::DepositRequest,
};
use alloy_primitives::{Address, Bloom, Log};
use core::cell::OnceCell;

/// Information externalized during block execution.
///
/// This struct is used to collect the results of executing a block of
/// transactions. It accumulates the receipts and senders of the transactions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockOutput<T: TxReceipt = ReceiptEnvelope> {
    /// The receipts of the transactions in the block, in order.
    receipts: Vec<T>,

    /// The senders of the transactions in the block, in order.
    senders: Vec<Address>,

    /// The logs bloom of the block.
    bloom: OnceCell<Bloom>,
}

impl Default for BlockOutput {
    fn default() -> Self {
        Self::with_capacity(0)
    }
}

impl<T: TxReceipt> BlockOutput<T> {
    /// Create a new block output with memory allocated to hold `capacity`
    /// transaction outcomes.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            receipts: Vec::with_capacity(capacity),
            senders: Vec::with_capacity(capacity),
            bloom: Default::default(),
        }
    }

    fn seal(&self) {
        self.bloom.get_or_init(|| {
            let mut bloom = Bloom::default();
            for log in self.logs() {
                bloom.accrue_log(log);
            }
            bloom
        });
    }

    fn unseal(&mut self) {
        self.bloom.take();
    }

    /// Reserve memory for `capacity` transaction outcomes.
    pub fn reserve(&mut self, capacity: usize) {
        self.receipts.reserve(capacity);
        self.senders.reserve(capacity);
    }

    /// Get a reference to the receipts of the transactions in the block.
    pub fn receipts(&self) -> &[T] {
        &self.receipts
    }

    /// Get an iterator over the logs of the transactions in the block.
    pub fn logs(&self) -> impl Iterator<Item = &Log> {
        self.receipts.iter().flat_map(|r| r.logs())
    }

    /// Get the logs bloom of the block.
    pub fn logs_bloom(&self) -> Bloom {
        self.seal();
        self.bloom.get().cloned().unwrap()
    }

    /// Get a reference the senders of the transactions in the block.
    pub fn senders(&self) -> &[Address] {
        &self.senders
    }

    /// Get the cumulative gas used in the block.
    pub fn cumulative_gas_used(&self) -> u128 {
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
    pub fn find_deposit_logs(&self) -> impl Iterator<Item = DepositRequest> + '_ {
        crate::system::eip6110::check_logs_for_deposits(
            self.receipts().iter().flat_map(TxReceipt::logs),
        )
    }

    /// Deconstruct the block output into its parts.
    pub fn into_parts(self) -> (Vec<T>, Vec<Address>, Bloom) {
        let bloom = self.logs_bloom();
        (self.receipts, self.senders, bloom)
    }
}
