use alloy_consensus::{Receipt, TxReceipt};
use alloy_primitives::{Address, Log};

/// Information externalized during block execution.
///
/// This struct is used to collect the results of executing a block of
/// transactions. It contains the receipts and senders of the transactions, as
/// well as any [`Request`] objects that were generated during the block.

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockOutput<T: TxReceipt = Receipt> {
    /// The receipts of the transactions in the block, in order.
    receipts: Vec<T>,

    /// The senders of the transactions in the block, in order.
    senders: Vec<Address>,
}

impl<T: TxReceipt> Default for BlockOutput<T> {
    fn default() -> Self {
        Self::with_capacity(10)
    }
}

impl<T: TxReceipt> BlockOutput<T> {
    /// Create a new block output with memory allocated to hold `capacity`
    /// transaction outcomes.
    pub fn with_capacity(capacity: usize) -> Self {
        Self { receipts: Vec::with_capacity(capacity), senders: Vec::with_capacity(capacity) }
    }

    /// Get a reference to the receipts of the transactions in the block.
    pub fn receipts(&self) -> &[T] {
        &self.receipts
    }

    /// Get an iterator over the logs of the transactions in the block.
    pub fn logs(&self) -> impl Iterator<Item = &Log> {
        self.receipts.iter().flat_map(|r| r.logs())
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
        self.push_receipt(receipt);
        self.push_sender(sender);
    }

    // /// Push a request onto the list of requests.
    // pub fn push_request(&mut self, request: Request) {
    //     self.requests.push(request);
    // }

    // /// Extend the list of requests with a vector of requests.
    // pub fn extend_requests(&mut self, requests: Vec<Request>) {
    //     self.requests.extend(requests);
    // }

    /// Push a receipt onto the list of receipts.
    fn push_receipt(&mut self, receipt: T) {
        self.receipts.push(receipt);
    }

    /// Push a sender onto the list of senders.
    fn push_sender(&mut self, sender: Address) {
        self.senders.push(sender);
    }
}
