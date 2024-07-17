use alloy_consensus::Receipt;
use alloy_primitives::Address;

/// Information externalized during block execution.
///
/// Requests are not handled here, as they require outside configuration in the
/// form of the deposit address.
#[derive(Debug, Clone, Default)]
pub struct BlockOutput<T = Receipt> {
    /// The receipts of the transactions in the block, in order.
    receipts: Vec<T>,
    /// The cumulative gas used in the block.
    cumulative_gas_used: u128,
    /// The senders of the transactions in the block, in order.
    senders: Vec<Address>,
}

impl<T> BlockOutput<T> {
    /// Create a new block output with memory allocated to hold `capacity`
    /// transaction outcomes.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            receipts: Vec::with_capacity(capacity),
            cumulative_gas_used: 0,
            senders: Vec::with_capacity(capacity),
        }
    }

    /// Returns the receipts of the transactions in the block.
    pub fn receipts(&self) -> &[T] {
        &self.receipts
    }

    /// Push a receipt onto the list of receipts.
    pub fn push_receipt(&mut self, receipt: T) {
        self.receipts.push(receipt);
    }

    /// Returns the cumulative gas used in the block.
    pub fn cumulative_gas_used(&self) -> u128 {
        self.cumulative_gas_used
    }

    /// Consume gas from the block, incrementing the cumulative gas used.
    pub fn consume_gas(&mut self, gas: u128) {
        self.cumulative_gas_used += gas;
    }

    /// Returns the senders of the transactions in the block.
    pub fn senders(&self) -> &[Address] {
        &self.senders
    }

    /// Push a sender onto the list of senders.
    pub fn push_sender(&mut self, sender: Address) {
        self.senders.push(sender);
    }
}
