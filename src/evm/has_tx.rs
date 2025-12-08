use crate::{helpers::Ctx, EvmErrored, HasBlock, HasCfg, HasTx, Trevm, Tx};
use alloy::{
    eips::eip7825::MAX_TX_GAS_LIMIT_OSAKA,
    primitives::{Address, Bytes, U256},
};
use revm::{
    context::{result::EVMError, ContextSetters, ContextTr, Transaction as _, TxEnv},
    primitives::{hardfork::SpecId, TxKind},
    state::AccountInfo,
    Database, DatabaseRef, Inspector,
};

impl<Db, Insp, TrevmState> Trevm<Db, Insp, TrevmState>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
    TrevmState: HasTx,
{
    #[cfg(feature = "call")]
    pub(crate) fn try_with_call_filler<NewState: HasCfg + HasBlock>(
        self,
        filler: &crate::fillers::CallFiller,
        f: impl FnOnce(Self) -> Result<Trevm<Db, Insp, NewState>, EvmErrored<Db, Insp>>,
    ) -> Result<Trevm<Db, Insp, NewState>, EvmErrored<Db, Insp>> {
        // override all relevant env bits
        self.try_with_cfg(filler, |this| this.try_with_block(filler, f))
    }

    /// Convenience function to use the estimator to fill both Cfg and Tx, and
    /// run a fallible function.
    #[cfg(feature = "estimate_gas")]
    pub(crate) fn try_with_estimate_gas_filler<E>(
        self,
        filler: &crate::fillers::GasEstimationFiller,
        f: impl FnOnce(Self) -> Result<Self, EvmErrored<Db, Insp, E>>,
    ) -> Result<Self, EvmErrored<Db, Insp, E>> {
        self.try_with_cfg(filler, |this| this.try_with_tx(filler, f))
    }

    /// Get a reference to the loaded tx env that will be executed.
    pub fn tx(&self) -> &TxEnv {
        self.inner.tx()
    }
    /// True if the transaction is a simple transfer.
    pub fn is_transfer(&self) -> bool {
        self.inner.tx().input().is_empty() && self.to().is_call()
    }

    /// True if the transaction is a contract creation.
    pub fn is_create(&self) -> bool {
        self.to().is_create()
    }

    /// Get a reference to the transaction input data, which will be used as
    /// calldata or initcode during EVM execution.
    pub fn input(&self) -> &Bytes {
        self.tx().input()
    }

    /// Read the target of the transaction.
    pub fn to(&self) -> TxKind {
        self.tx().kind()
    }

    /// Read the value in wei of the transaction.
    pub fn value(&self) -> U256 {
        self.tx().value()
    }

    /// Get the gas limit of the loaded transaction.
    pub fn gas_limit(&self) -> u64 {
        self.tx().gas_limit()
    }

    /// Get the gas price of the loaded transaction.
    pub fn gas_price(&self) -> u128 {
        self.tx().gas_price()
    }

    /// Get the address of the caller.
    pub fn caller(&self) -> Address {
        self.tx().caller()
    }

    /// Get the account of the caller. Error if the DB errors.
    pub fn caller_account(&mut self) -> Result<AccountInfo, EVMError<<Db as Database>::Error>> {
        self.try_read_account(self.caller())
            .map(Option::unwrap_or_default)
            .map_err(EVMError::Database)
    }

    /// Get the address of the callee. `None` if `Self::is_create` is true.
    pub fn callee(&self) -> Option<Address> {
        self.to().into()
    }

    /// Get the account of the callee.
    ///
    /// Returns as follows:
    /// - if `Self::is_create` is true, `Ok(None)`
    /// - if the callee account does not exist, `Ok(AccountInfo::default())`
    /// - if the DB errors, `Err(EVMError::Database(err))`
    pub fn callee_account(
        &mut self,
    ) -> Result<Option<AccountInfo>, EVMError<<Db as Database>::Error>> {
        self.callee().map_or(Ok(None), |addr| {
            self.try_read_account(addr)
                .map(Option::unwrap_or_default)
                .map(Some)
                .map_err(EVMError::Database)
        })
    }

    /// Get the account of the callee. `None` if `Self::is_create` is true,
    /// error if the DB errors.
    pub fn callee_account_ref(&self) -> Result<Option<AccountInfo>, <Db as DatabaseRef>::Error>
    where
        Db: DatabaseRef,
    {
        self.callee().map_or(Ok(None), |addr| self.try_read_account_ref(addr))
    }

    /// Run a function with the provided transaction, then restore the previous
    /// transaction.
    pub fn with_tx<T, F, NewState>(mut self, t: &T, f: F) -> Trevm<Db, Insp, NewState>
    where
        T: Tx,
        F: FnOnce(Self) -> Trevm<Db, Insp, NewState>,
        NewState: HasTx,
    {
        let previous = self.inner.tx().clone();
        t.fill_tx(&mut self.inner);
        let mut this = f(self);
        this.inner.ctx.set_tx(previous);
        this
    }

    /// Run a fallible function with the provided transaction, then restore the
    /// previous transaction.
    pub fn try_with_tx<T, F, NewState, E>(
        mut self,
        t: &T,
        f: F,
    ) -> Result<Trevm<Db, Insp, NewState>, EvmErrored<Db, Insp, E>>
    where
        T: Tx,
        F: FnOnce(Self) -> Result<Trevm<Db, Insp, NewState>, EvmErrored<Db, Insp, E>>,
        NewState: HasTx,
    {
        let previous = self.inner.tx().clone();
        t.fill_tx(&mut self.inner);
        match f(self) {
            Ok(mut evm) => {
                evm.inner.ctx.set_tx(previous);
                Ok(evm)
            }
            Err(mut evm) => {
                evm.inner.ctx.set_tx(previous);
                Err(evm)
            }
        }
    }

    /// Return the maximum gas that the caller can purchase. This is the balance
    /// of the caller divided by the gas price.
    pub fn caller_gas_allowance(&mut self) -> Result<u64, EVMError<<Db as Database>::Error>> {
        // Avoid DB read if gas price is zero
        let gas_price = self.gas_price();
        self.try_gas_allowance(self.caller(), gas_price).map_err(EVMError::Database)
    }

    /// This function caps the gas limit of the transaction to the allowance of
    /// the caller.
    ///
    /// This is useful for e.g. call simulation, where the exact amount of gas
    /// used is less important than ensuring that the call succeeds and returns
    /// a meaningful result.
    ///
    /// # Returns
    ///
    /// The gas limit after the operation.
    pub fn cap_tx_gas_to_allowance(&mut self) -> Result<u64, EVMError<<Db as Database>::Error>> {
        let allowance = self.caller_gas_allowance()?;

        self.inner.modify_tx(|tx| tx.gas_limit = tx.gas_limit.min(allowance));

        Ok(self.gas_limit())
    }

    /// Cap the gas limit of the transaction to the minimum of the block gas
    /// limit and the transaction's gas limit.
    ///
    /// This is useful for ensuring that the transaction does not exceed the
    /// block gas limit, e.g. during call simulation.
    ///
    /// # Returns
    ///
    /// The gas limit after the operation.
    pub fn cap_tx_gas_to_block_limit(&mut self) -> u64 {
        let block_gas_limit = self.block_gas_limit();

        self.inner.modify_tx(|tx| tx.gas_limit = tx.gas_limit.min(block_gas_limit));

        self.tx().gas_limit
    }

    /// This function caps the gas limit of the transaction to the minimum of
    /// the block limit and the caller's gas allowance.
    ///
    /// This is equivalent to calling [`Self::cap_tx_gas_to_block_limit`] and
    /// [`Self::cap_tx_gas_to_allowance`] in sequence.
    ///
    /// # Returns
    ///
    /// The gas limit after the operation.
    pub fn cap_tx_gas(&mut self) -> Result<u64, EVMError<<Db as Database>::Error>> {
        self.cap_tx_gas_to_block_limit();

        // If the currently active SpecId is Osaka or greater, also attempt to cap the gas limit to the EIP-7825 limit.
        if self.spec_id() >= SpecId::OSAKA {
            self.cap_tx_gas_to_eip7825();
        }

        self.cap_tx_gas_to_allowance()
    }

    /// Cap the gas limit of the transaction to the [`EIP-7825`] limit.
    ///
    /// # Returns
    ///
    /// The gas limit after the operation.
    ///
    /// [`EIP-7825`]: https://eips.ethereum.org/EIPS/eip-7825
    pub fn cap_tx_gas_to_eip7825(&mut self) -> u64 {
        self.inner.modify_tx(|tx| tx.gas_limit = tx.gas_limit.min(MAX_TX_GAS_LIMIT_OSAKA));

        self.tx().gas_limit
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fillers::DisableChainIdCheck,
        test_utils::{test_trevm_with_funds, ALICE, BOB, LOG_DEPLOYED_BYTECODE},
        NoopBlock, NoopCfg, TrevmBuilder,
    };
    use alloy::{
        consensus::constants::ETH_TO_WEI,
        network::{TransactionBuilder, TransactionBuilder7702},
        primitives::{Address, U256},
        rpc::types::{Authorization, TransactionRequest},
        signers::SignerSync,
    };
    use revm::{
        context::transaction::AuthorizationTr,
        database::InMemoryDB,
        primitives::{bytes, hardfork::SpecId},
        state::Bytecode,
    };

    #[test]
    fn test_estimate_gas_simple_transfer() {
        let trevm = test_trevm_with_funds(&[
            (ALICE.address(), U256::from(ETH_TO_WEI)),
            (BOB.address(), U256::from(ETH_TO_WEI)),
        ]);

        let tx = TransactionRequest::default()
            .from(ALICE.address())
            .to(BOB.address())
            .value(U256::from(ETH_TO_WEI / 2));

        let (estimation, _trevm) =
            trevm.fill_cfg(&NoopCfg).fill_block(&NoopBlock).fill_tx(&tx).estimate_gas().unwrap();

        assert!(estimation.is_success());
        // The gas used should correspond to a simple transfer.
        assert_eq!(estimation.gas_used(), 21000);
    }

    #[test]
    fn test_7702_authorization_estimation() {
        // Insert the LogContract code
        let db = InMemoryDB::default();
        let log_address = Address::repeat_byte(0x32);

        // Set up trevm, and test balances.
        let mut trevm = TrevmBuilder::new().with_db(db).with_spec_id(SpecId::OSAKA).build_trevm();
        let _ = trevm.test_set_balance(ALICE.address(), U256::from(ETH_TO_WEI));
        let _ = trevm.set_bytecode_unchecked(log_address, Bytecode::new_raw(LOG_DEPLOYED_BYTECODE));

        // Bob will sign the authorization.
        let authorization = Authorization {
            chain_id: U256::ZERO,
            address: log_address,
            // We know Bob's nonce is 0.
            nonce: 0,
        };
        let signature = BOB.sign_hash_sync(&authorization.signature_hash()).unwrap();
        let signed_authorization = authorization.into_signed(signature);
        assert_eq!(signed_authorization.authority().unwrap(), BOB.address());

        let tx = TransactionRequest::default()
            .from(ALICE.address())
            .to(BOB.address())
            .with_authorization_list(vec![signed_authorization])
            .with_input(bytes!("0x7b3ab2d0")); // emitHello()

        let (estimation, trevm) = trevm
            .fill_cfg(&DisableChainIdCheck)
            .fill_block(&NoopBlock)
            .fill_tx(&tx)
            .estimate_gas()
            .unwrap();

        assert!(estimation.is_success());

        let tx = tx.with_gas_limit(estimation.limit());

        let output = trevm.clear_tx().fill_tx(&tx).run().unwrap().accept();

        assert!(output.0.is_success());
        assert_eq!(output.0.logs().len(), 1);
    }
}

// Some code above and documentation is adapted from the revm crate, and is
// reproduced here under the terms of the MIT license.
//
// MIT License
//
// Copyright (c) 2021-2024 draganrakita
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
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
