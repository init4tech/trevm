use alloy::consensus::{Receipt, ReceiptWithBloom};
use revm::primitives::ExecutionResult;

/// Create an Ethereum [`ReceiptEnvelope`] from an execution result.
///
/// [`ReceiptEnvelope`]: alloy::consensus::ReceiptEnvelope
pub fn ethereum_receipt(result: ExecutionResult, prior_gas_used: u128) -> ReceiptWithBloom {
    let cumulative_gas_used = prior_gas_used.saturating_add(result.gas_used() as u128);

    Receipt { status: result.is_success().into(), cumulative_gas_used, logs: result.into_logs() }
        .into()
}
