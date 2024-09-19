use alloy::{consensus::ReceiptEnvelope, eips::eip6110::DepositRequest};
use alloy_primitives::Log;
use alloy_sol_types::{sol, SolEvent};

/// The address for the Ethereum 2.0 deposit contract on the mainnet.
pub use alloy::eips::eip6110::MAINNET_DEPOSIT_CONTRACT_ADDRESS;

sol! {
    #[allow(missing_docs)]
    event DepositEvent(
        bytes pubkey,
        bytes withdrawal_credentials,
        bytes amount,
        bytes signature,
        bytes index
    );
}

/// Parse deposit requests from logs.
///
/// When parsing logs, the following assumptions are made
///
/// - The `DepositEvent` is the only event in the deposit contract.
/// - The deposit contract enforces the length of the fields.
pub fn parse_deposit_from_log(log: &Log<DepositEvent>) -> DepositRequest {
    // SAFETY: These `expect` https://github.com/ethereum/consensus-specs/blob/5f48840f4d768bf0e0a8156a3ed06ec333589007/solidity_deposit_contract/deposit_contract.sol#L107-L110
    // are safe because the `DepositEvent` is the only event in the deposit contract and the length
    // checks are done there.
    DepositRequest {
        pubkey: log
            .pubkey
            .as_ref()
            .try_into()
            .expect("pubkey length should be enforced in deposit contract"),
        withdrawal_credentials: log
            .withdrawal_credentials
            .as_ref()
            .try_into()
            .expect("withdrawal_credentials length should be enforced in deposit contract"),
        amount: u64::from_le_bytes(
            log.amount
                .as_ref()
                .try_into()
                .expect("amount length should be enforced in deposit contract"),
        ),
        signature: log
            .signature
            .as_ref()
            .try_into()
            .expect("signature length should be enforced in deposit contract"),
        index: u64::from_le_bytes(
            log.index
                .as_ref()
                .try_into()
                .expect("deposit index length should be enforced in deposit contract"),
        ),
    }
}

/// Check an iterator of logs for deposit events, parsing them into
/// [`DepositRequest`]s.
///
/// When parsing logs, the following assumptions are made
///
/// - The `DepositEvent` is the only event in the deposit contract.
/// - The deposit contract enforces the length of the fields.
pub fn check_logs_for_deposits<'a, I>(logs: I) -> impl Iterator<Item = DepositRequest> + 'a
where
    I: IntoIterator<Item = &'a Log>,
    I::IntoIter: 'a,
{
    logs.into_iter().filter(|log| log.address == MAINNET_DEPOSIT_CONTRACT_ADDRESS).map(|log| {
        // We assume that the log is valid because it was emitted by the
        // deposit contract.
        let decoded_log = DepositEvent::decode_log(log, false).expect("invalid log");
        parse_deposit_from_log(&decoded_log)
    })
}

/// Find deposit logs in a receipt. Iterates over the logs in the receipt and
/// returns a [`DepositRequest`] for each log that is emitted by the
/// deposit contract.
///
/// When parsing logs, the following assumptions are made
///
/// - The `DepositEvent` is the only event in the deposit contract.
/// - The deposit contract enforces the length of the fields.
pub fn check_receipt_for_deposits(
    receipt: &ReceiptEnvelope,
) -> impl Iterator<Item = DepositRequest> + '_ {
    check_logs_for_deposits(receipt.logs())
}

// Some code above is reproduced from `reth`. It is reused here under the MIT
// license.
//
// The MIT License (MIT)
//
// Copyright (c) 2022-2024 Reth Contributors
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

#[cfg(test)]
mod test {
    use alloy::{
        consensus::{Receipt, ReceiptEnvelope},
        eips::eip6110::MAINNET_DEPOSIT_CONTRACT_ADDRESS,
    };
    use alloy_primitives::{Log, LogData};
    use alloy_sol_types::SolEvent;

    use super::DepositEvent;

    #[test]
    fn test_eip6110() {
        let receipt = Receipt {
            logs: vec![Log {
                address: MAINNET_DEPOSIT_CONTRACT_ADDRESS,
                data: LogData::new_unchecked(
                    vec![DepositEvent::SIGNATURE_HASH],
                    DepositEvent {
                        pubkey: [1; 48].to_vec().into(),
                        withdrawal_credentials: [2; 32].to_vec().into(),
                        amount: [3; 8].to_vec().into(),
                        signature: [4; 96].to_vec().into(),
                        index: [5; 8].to_vec().into(),
                    }
                    .encode_data()
                    .into(),
                ),
            }],
            status: true.into(),
            cumulative_gas_used: 0,
        };

        let deposits: Vec<_> =
            super::check_receipt_for_deposits(&ReceiptEnvelope::Eip1559(receipt.into())).collect();

        assert_eq!(deposits.len(), 1);
        assert_eq!(deposits[0].pubkey, [1; 48]);
        assert_eq!(deposits[0].withdrawal_credentials, [2; 32]);
        assert_eq!(deposits[0].amount, 0x0303030303030303);
        assert_eq!(deposits[0].signature, [4; 96]);
        assert_eq!(deposits[0].index, 0x0505050505050505);
    }
}
