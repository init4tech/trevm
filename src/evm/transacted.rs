use crate::{
    helpers::Ctx, EvmErrored, EvmNeedsTx, EvmReady, EvmTransacted, NeedsTx, TransactedState, Trevm,
};
use alloy::primitives::Bytes;
use revm::{
    context::{
        result::{ExecutionResult, ResultAndState},
        ContextTr,
    },
    database::TryDatabaseCommit,
    state::EvmState,
    Database, DatabaseCommit, Inspector,
};

impl<Db, Insp> AsRef<ResultAndState> for EvmTransacted<Db, Insp>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    fn as_ref(&self) -> &ResultAndState {
        &self.state.result
    }
}

impl<Db, Insp> AsRef<ExecutionResult> for EvmTransacted<Db, Insp>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    fn as_ref(&self) -> &ExecutionResult {
        &self.state.result.result
    }
}

impl<Db, Insp> EvmTransacted<Db, Insp>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    /// Get a reference to the result.
    pub fn result(&self) -> &ExecutionResult {
        self.as_ref()
    }

    /// Get a mutable reference to the result. Modification of the result is
    /// discouraged, as it may lead to inconsistent state.
    ///
    /// This is primarily intended for use in [`SystemTx`] execution.
    ///
    /// [`SystemTx`]: crate::system::SystemTx
    pub const fn result_mut_unchecked(&mut self) -> &mut ExecutionResult {
        &mut self.state.result.result
    }

    /// Get a reference to the state.
    pub const fn state(&self) -> &EvmState {
        &self.state.result.state
    }

    /// Get a mutable reference to the state. Modification of the state is
    /// discouraged, as it may lead to inconsistent state.
    pub const fn state_mut_unchecked(&mut self) -> &mut EvmState {
        &mut self.state.result.state
    }

    /// Get a reference to the result and state.
    pub fn result_and_state(&self) -> &ResultAndState {
        self.as_ref()
    }

    /// Get a mutable reference to the result and state. Modification of the
    /// result and state is discouraged, as it may lead to inconsistent state.
    ///
    /// This is primarily intended for use in [`SystemTx`] execution.
    ///
    /// [`SystemTx`]: crate::system::SystemTx
    pub const fn result_and_state_mut_unchecked(&mut self) -> &mut ResultAndState {
        &mut self.state.result
    }

    /// Get the output of the transaction. This is the return value of the
    /// outermost callframe.
    pub fn output(&self) -> Option<&Bytes> {
        self.result().output()
    }

    /// Get the output of the transaction, and decode it as the return value of
    /// a [`SolCall`]. If `validate` is true, the output will be type- and
    /// range-checked.
    ///
    /// [`SolCall`]: alloy::sol_types::SolCall
    pub fn output_sol<T: alloy::sol_types::SolCall>(
        &self,
        validate: bool,
    ) -> Option<alloy::sol_types::Result<T::Return>>
    where
        T::Return: alloy::sol_types::SolType,
    {
        if validate {
            return self.output().map(|output| T::abi_decode_returns_validate(output));
        }

        self.output().map(|output| T::abi_decode_returns(output))
    }

    /// Get the gas used by the transaction.
    pub fn gas_used(&self) -> u64 {
        self.state.result.result.gas_used()
    }

    /// Discard the state changes and return the EVM.
    pub fn reject(self) -> EvmNeedsTx<Db, Insp> {
        Trevm { inner: self.inner, state: NeedsTx::new() }
    }

    /// Take the [`ResultAndState`] and return the EVM.
    pub fn into_result_and_state(self) -> ResultAndState {
        self.state.result
    }

    /// Take the [`ResultAndState`] and return the EVM.
    pub fn take_result_and_state(self) -> (ResultAndState, EvmNeedsTx<Db, Insp>) {
        let Self { inner, state: TransactedState { result } } = self;
        (result, Trevm { inner, state: NeedsTx::new() })
    }

    /// Take the [`ExecutionResult`], discard the [`EvmState`] and return the
    /// EVM.
    pub fn take_result(self) -> (ExecutionResult, EvmNeedsTx<Db, Insp>) {
        let Self { inner, state: TransactedState { result } } = self;
        (result.result, Trevm { inner, state: NeedsTx::new() })
    }

    /// Accept the state changes, commiting them to the database, and return the
    /// EVM with the [`ExecutionResult`].
    pub fn accept(self) -> (ExecutionResult, EvmNeedsTx<Db, Insp>)
    where
        Db: DatabaseCommit,
    {
        let Self { mut inner, state: TransactedState { result } } = self;

        inner.db_mut().commit(result.state);

        (result.result, Trevm { inner, state: NeedsTx::new() })
    }

    /// Try to accept the state changes, commiting them to the database, and
    /// return the EVM with the [`ExecutionResult`]. If the commit fails, return
    /// the EVM with the error, discarding the state changes. This is a fallible
    /// version of [`Self::accept`], intended for use with databases that can
    /// fail to commit. Prefer [`Self::accept`] when possible.
    // Type alias would make it less clear I think
    #[allow(clippy::type_complexity)]
    pub fn try_accept(
        self,
    ) -> Result<
        (ExecutionResult, EvmNeedsTx<Db, Insp>),
        EvmErrored<Db, Insp, <Db as TryDatabaseCommit>::Error>,
    >
    where
        Db: TryDatabaseCommit,
    {
        let Self { mut inner, state: TransactedState { result } } = self;

        trevm_try!(inner.db_mut().try_commit(result.state), Trevm { inner, state: NeedsTx::new() });

        Ok((result.result, Trevm { inner, state: NeedsTx::new() }))
    }

    /// Accept the state changes, commiting them to the database, dropping the
    /// [`ExecutionResult`].
    pub fn accept_state(self) -> EvmNeedsTx<Db, Insp>
    where
        Db: DatabaseCommit,
    {
        self.accept().1
    }

    /// Try to accept the state changes, commiting them to the database. If the
    /// commit fails, return the EVM with the error, discarding the state
    /// changes. This is a fallible version of [`Self::accept_state`], intended
    /// for use with databases that can fail to commit. Prefer
    /// [`Self::accept_state`] when possible.
    pub fn try_accept_state(
        self,
    ) -> Result<EvmNeedsTx<Db, Insp>, EvmErrored<Db, Insp, <Db as TryDatabaseCommit>::Error>>
    where
        Db: TryDatabaseCommit,
    {
        self.try_accept().map(|(_, evm)| evm)
    }

    /// Create an [`EstimationResult`] from the transaction [`ExecutionResult`].
    ///
    /// [`EstimationResult`]: crate::EstimationResult
    #[cfg(feature = "estimate_gas")]
    pub fn estimation(&self) -> crate::EstimationResult {
        use crate::EstimationResult;

        EstimationResult::from_limit_and_execution_result(self.gas_limit(), self.result())
    }

    /// Take the [`EstimationResult`] and return it and the EVM. This discards
    /// pending state changes, but leaves the EVM ready to execute the same
    /// transaction again.
    ///
    /// [`EstimationResult`]: crate::EstimationResult
    #[cfg(feature = "estimate_gas")]
    pub fn take_estimation(self) -> (crate::EstimationResult, EvmReady<Db, Insp>) {
        let estimation = self.estimation();
        (estimation, Trevm { inner: self.inner, state: crate::Ready::new() })
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
