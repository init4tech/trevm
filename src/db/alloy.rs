use alloy::{
    eips::BlockId,
    primitives::{StorageValue, U256},
    providers::{
        network::{primitives::HeaderResponse, BlockResponse},
        Network, Provider,
    },
    transports::TransportError,
};
use core::error::Error;
use revm::{
    database_interface::{async_db::DatabaseAsyncRef, DBErrorMarker},
    primitives::{Address, B256},
    state::{AccountInfo, Bytecode},
};
use std::fmt::Display;

/// A type alias for the storage key used in the database.
/// We use this instead of alloy's [`alloy::primitives::StorageKey`] as Revm requires
/// the actual type to be an [`U256`] instead of a [`B256`].
pub type StorageKey = U256;

/// An error that can occur when using [`AlloyDb`].
#[derive(Debug)]
pub struct DBTransportError(pub TransportError);

impl DBErrorMarker for DBTransportError {}

impl Display for DBTransportError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Transport error: {}", self.0)
    }
}

impl Error for DBTransportError {}

impl From<TransportError> for DBTransportError {
    fn from(e: TransportError) -> Self {
        Self(e)
    }
}

/// An alloy-powered REVM [`Database`][revm::database_interface::Database].
///
/// When accessing the database, it'll use the given provider to fetch the corresponding account's data.
#[derive(Debug)]
pub struct AlloyDb<N: Network, P: Provider<N>> {
    /// The provider to fetch the data from.
    provider: P,
    /// The block number on which the queries will be based on.
    block_number: BlockId,
    _marker: core::marker::PhantomData<fn() -> N>,
}

impl<N: Network, P: Provider<N>> AlloyDb<N, P> {
    /// Creates a new AlloyDB instance, with a [`Provider`] and a block.
    pub fn new(provider: P, block_number: BlockId) -> Self {
        Self { provider, block_number, _marker: core::marker::PhantomData }
    }

    /// Sets the block number on which the queries will be based on.
    pub const fn set_block_number(&mut self, block_number: BlockId) {
        self.block_number = block_number;
    }
}

impl<N: Network, P: Provider<N>> DatabaseAsyncRef for AlloyDb<N, P> {
    type Error = DBTransportError;

    async fn basic_async_ref(&self, address: Address) -> Result<Option<AccountInfo>, Self::Error> {
        let nonce = self.provider.get_transaction_count(address).block_id(self.block_number);
        let balance = self.provider.get_balance(address).block_id(self.block_number);
        let code = self.provider.get_code_at(address).block_id(self.block_number);

        let (nonce, balance, code) = tokio::join!(nonce, balance, code,);

        let balance = balance?;
        let code = Bytecode::new_raw(code?.0.into());
        let code_hash = code.hash_slow();
        let nonce = nonce?;

        Ok(Some(AccountInfo::new(balance, nonce, code_hash, code)))
    }

    async fn block_hash_async_ref(&self, number: u64) -> Result<B256, Self::Error> {
        let block = self
            .provider
            // SAFETY: We know number <= u64::MAX, so we can safely convert it to u64
            .get_block_by_number(number.into())
            .await?;
        // SAFETY: If the number is given, the block is supposed to be finalized, so unwrapping is safe.
        Ok(B256::new(*block.unwrap().header().hash()))
    }

    async fn code_by_hash_async_ref(&self, _code_hash: B256) -> Result<Bytecode, Self::Error> {
        panic!("This should not be called, as the code is already loaded");
        // This is not needed, as the code is already loaded with basic_ref
    }

    async fn storage_async_ref(
        &self,
        address: Address,
        index: StorageKey,
    ) -> Result<StorageValue, Self::Error> {
        Ok(self.provider.get_storage_at(address, index).block_id(self.block_number).await?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy::providers::ProviderBuilder;
    use revm::database_interface::{DatabaseRef, WrapDatabaseAsync};

    #[test]
    #[ignore = "flaky RPC"]
    fn can_get_basic() {
        let client = ProviderBuilder::new().connect_http(
            "https://mainnet.infura.io/v3/c60b0bb42f8a4c6481ecd229eddaca27".parse().unwrap(),
        );
        let alloydb = AlloyDb::new(client, BlockId::from(16148323));
        let wrapped_alloydb = WrapDatabaseAsync::new(alloydb).unwrap();

        // ETH/USDT pair on Uniswap V2
        let address: Address = "0x0d4a11d5EEaaC28EC3F61d100daF4d40471f1852".parse().unwrap();

        let acc_info = wrapped_alloydb.basic_ref(address).unwrap().unwrap();
        assert!(acc_info.exists());
    }
}

// This code has been reproduced from the original AlloyDB implementation
// contained in revm.
// <https://github.com/bluealloy/revm>
// The original license is included below:
//
// MIT License
// Copyright (c) 2021-2025 draganrakita
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
