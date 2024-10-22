use alloc::vec::Vec;
use alloy::consensus::ReceiptEnvelope;
use alloy_primitives::{Bytes, Log};
use alloy_rlp::BufMut;
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
pub fn parse_deposit_from_log(log: &Log<DepositEvent>) -> Bytes {
    [
        log.pubkey.as_ref(),
        log.withdrawal_credentials.as_ref(),
        log.amount.as_ref(),
        log.signature.as_ref(),
        log.index.as_ref(),
    ]
    .concat()
    .into()
}

/// Accumulate a deposit request from a log.
pub fn accumulate_deposit_from_log(log: &Log<DepositEvent>, out: &mut dyn BufMut) {
    out.put_slice(log.pubkey.as_ref());
    out.put_slice(log.withdrawal_credentials.as_ref());
    out.put_slice(log.amount.as_ref());
    out.put_slice(log.signature.as_ref());
    out.put_slice(log.index.as_ref());
}

/// Check an iterator of logs for deposit events.
///
/// When parsing logs, the following assumptions are made
///
/// - The `DepositEvent` is the only event in the deposit contract.
/// - The deposit contract enforces the length of the fields.
pub fn check_logs_for_deposits<'a, I>(logs: I) -> impl Iterator<Item = Bytes> + 'a
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

/// Accumulate deposits from an iterator of logs.
pub fn accumulate_deposits_from_logs<'a>(
    logs: impl IntoIterator<Item = &'a Log>,
    out: &mut dyn BufMut,
) {
    logs.into_iter().filter(|log| log.address == MAINNET_DEPOSIT_CONTRACT_ADDRESS).for_each(
        |log| {
            // We assume that the log is valid because it was emitted by the
            // deposit contract.
            let decoded_log = DepositEvent::decode_log(log, false).expect("invalid log");
            accumulate_deposit_from_log(&decoded_log, out);
        },
    );
}

/// Find deposit logs in a receipt. Iterates over the logs in the receipt and
/// returns a deposit request bytestring for each log that is emitted by the
/// deposit contract.
///
/// When parsing logs, the following assumptions are made
///
/// - The `DepositEvent` is the only event in the deposit contract.
/// - The deposit contract enforces the length of the fields.
pub fn check_receipt_for_deposits(
    receipt: &ReceiptEnvelope,
) -> impl Iterator<Item = Bytes> + use<'_> {
    check_logs_for_deposits(receipt.logs())
}

/// Accumulate deposits from a receipt. Iterates over the logs in the receipt
/// and accumulates the deposit request bytestrings.
pub fn accumulate_deposits_from_receipt(receipt: &ReceiptEnvelope, out: &mut dyn BufMut) {
    accumulate_deposits_from_logs(receipt.logs(), out);
}

/// Accumulate deposits from a list of receipts. Iterates over the logs in the
/// receipts and accumulates the deposit request bytestrings.
pub fn accumulate_deposits_from_receipts<'a, I>(receipts: I, out: &mut dyn BufMut)
where
    I: IntoIterator<Item = &'a ReceiptEnvelope>,
{
    receipts.into_iter().for_each(|receipt| accumulate_deposits_from_receipt(receipt, out));
}

/// Find deposit logs in a list of receipts, and return the concatenated
/// deposit request bytestring.
pub fn deposits_from_receipts<'a, I>(receipts: I) -> Bytes
where
    I: IntoIterator<Item = &'a ReceiptEnvelope>,
{
    let mut out = Vec::new();
    accumulate_deposits_from_receipts(receipts, &mut out);
    out.into()
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
mod tests {
    use super::*;
    use alloc::vec;
    use alloy::consensus::{Receipt, ReceiptEnvelope};
    use alloy_primitives::bytes;

    #[test]
    fn test_parse_deposit_from_log() {
        let receipts = vec![
            // https://etherscan.io/tx/0xa5239d4c542063d29022545835815b78b09f571f2bf1c8427f4765d6f5abbce9
            #[allow(clippy::needless_update)] // side-effect of optimism fields
            ReceiptEnvelope::Legacy(Receipt {
                // these don't matter
                status: true.into(),
                cumulative_gas_used: 0,
                logs: serde_json::from_str(
                    r#"[{"address":"0x00000000219ab540356cbb839cbe05303d7705fa","topics":["0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5"],"data":"0x00000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000018000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000030998c8086669bf65e24581cda47d8537966e9f5066fc6ffdcba910a1bfb91eae7a4873fcce166a1c4ea217e6b1afd396200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002001000000000000000000000001c340fb72ed14d4eaa71f7633ee9e33b88d4f3900000000000000000000000000000000000000000000000000000000000000080040597307000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006098ddbffd700c1aac324cfdf0492ff289223661eb26718ce3651ba2469b22f480d56efab432ed91af05a006bde0c1ea68134e0acd8cacca0c13ad1f716db874b44abfcc966368019753174753bca3af2ea84bc569c46f76592a91e97f311eddec0000000000000000000000000000000000000000000000000000000000000008e474160000000000000000000000000000000000000000000000000000000000","blockHash":"0x8d1289c5a7e0965b1d1bb75cdc4c3f73dda82d4ebb94ff5b98d1389cebd53b56","blockNumber":"0x12f0d8d","transactionHash":"0xa5239d4c542063d29022545835815b78b09f571f2bf1c8427f4765d6f5abbce9","transactionIndex":"0xc4","logIndex":"0x18f","removed":false}]"#
                ).unwrap(),
                ..Default::default()
            }.with_bloom()),
            // https://etherscan.io/tx/0xd9734d4e3953bcaa939fd1c1d80950ee54aeecc02eef6ae8179f47f5b7103338
            #[allow(clippy::needless_update)] // side-effect of optimism fields
            ReceiptEnvelope::Legacy(Receipt {
                // these don't matter
                status: true.into(),
                cumulative_gas_used: 0,
                logs: serde_json::from_str(
                    r#"[{"address":"0x00000000219ab540356cbb839cbe05303d7705fa","topics":["0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5"],"data":"0x00000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000018000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000030a1a2ba870a90e889aa594a0cc1c6feffb94c2d8f65646c937f1f456a315ef649533e25a4614d8f4f66ebdb06481b90af0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200100000000000000000000000a0f04a231efbc29e1db7d086300ff550211c2f6000000000000000000000000000000000000000000000000000000000000000800405973070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060ad416d590e1a7f52baff770a12835b68904efad22cc9f8ba531e50cbbd26f32b9c7373cf6538a0577f501e4d3e3e63e208767bcccaae94e1e3720bfb734a286f9c017d17af46536545ccb7ca94d71f295e71f6d25bf978c09ada6f8d3f7ba0390000000000000000000000000000000000000000000000000000000000000008e374160000000000000000000000000000000000000000000000000000000000","blockHash":"0x8d1289c5a7e0965b1d1bb75cdc4c3f73dda82d4ebb94ff5b98d1389cebd53b56","blockNumber":"0x12f0d8d","transactionHash":"0xd9734d4e3953bcaa939fd1c1d80950ee54aeecc02eef6ae8179f47f5b7103338","transactionIndex":"0x7c","logIndex":"0xe2","removed":false}]"#,
                ).unwrap(),
                ..Default::default()
            }.with_bloom()),
        ];

        let request_data = deposits_from_receipts(&receipts);
        assert_eq!(
            request_data,
            bytes!(
                "998c8086669bf65e24581cda47d8537966e9f5066fc6ffdcba910a1bfb91eae7a4873fcce166a1c4ea217e6b1afd396201000000000000000000000001c340fb72ed14d4eaa71f7633ee9e33b88d4f39004059730700000098ddbffd700c1aac324cfdf0492ff289223661eb26718ce3651ba2469b22f480d56efab432ed91af05a006bde0c1ea68134e0acd8cacca0c13ad1f716db874b44abfcc966368019753174753bca3af2ea84bc569c46f76592a91e97f311eddece474160000000000a1a2ba870a90e889aa594a0cc1c6feffb94c2d8f65646c937f1f456a315ef649533e25a4614d8f4f66ebdb06481b90af0100000000000000000000000a0f04a231efbc29e1db7d086300ff550211c2f60040597307000000ad416d590e1a7f52baff770a12835b68904efad22cc9f8ba531e50cbbd26f32b9c7373cf6538a0577f501e4d3e3e63e208767bcccaae94e1e3720bfb734a286f9c017d17af46536545ccb7ca94d71f295e71f6d25bf978c09ada6f8d3f7ba039e374160000000000"
            )
        );
    }
}
