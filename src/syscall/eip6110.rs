use alloy_eips::eip6110::DepositRequest;
use alloy_primitives::{address, Address, Log};
use alloy_sol_types::sol;

pub const MAINNET_DEPOSIT_ADDRESS: Address = address!("00000000219ab540356cbb839cbe05303d7705fa");

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
