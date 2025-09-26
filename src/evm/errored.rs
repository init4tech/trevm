use crate::{helpers::Ctx, ErroredState, EvmErrored, EvmNeedsTx, NeedsTx, Trevm};
use revm::{
    context::result::{EVMError, InvalidTransaction},
    Database, Inspector,
};

impl<Db, Insp, E> EvmErrored<Db, Insp, E>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    /// Get a reference to the error.
    pub const fn error(&self) -> &E {
        &self.state.error
    }

    /// Inspect the error with a closure.
    pub fn inspect_err<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&E) -> T,
    {
        f(self.error())
    }

    /// Discard the error and return the EVM.
    pub fn discard_error(self) -> EvmNeedsTx<Db, Insp> {
        Trevm { inner: self.inner, state: NeedsTx::new() }
    }

    /// Convert the error into an [`EVMError`].
    pub fn into_error(self) -> E {
        self.state.error
    }

    /// Reset the EVM, returning the error and the EVM ready for the next
    /// transaction.
    pub fn take_err(self) -> (E, EvmNeedsTx<Db, Insp>) {
        let Self { inner, state: ErroredState { error } } = self;
        (error, Trevm { inner, state: NeedsTx::new() })
    }

    /// Transform the error into a new error type.
    pub fn err_into<NewErr: From<E>>(self) -> EvmErrored<Db, Insp, NewErr> {
        self.map_err(Into::into)
    }

    /// Map the error to a new error type.
    pub fn map_err<F, NewErr>(self, f: F) -> EvmErrored<Db, Insp, NewErr>
    where
        F: FnOnce(E) -> NewErr,
    {
        Trevm { inner: self.inner, state: ErroredState { error: f(self.state.error) } }
    }
}

impl<Db, Insp> EvmErrored<Db, Insp>
where
    Db: Database,
    Insp: Inspector<Ctx<Db>>,
{
    /// Check if the error is a transaction error. This is provided as a
    /// convenience function for common cases, as Transaction errors should
    /// usually be discarded.
    pub const fn is_transaction_error(&self) -> bool {
        matches!(self.state.error, EVMError::Transaction(_))
    }

    /// Fallible cast to a [`InvalidTransaction`].
    pub const fn as_transaction_error(&self) -> Option<&InvalidTransaction> {
        match &self.state.error {
            EVMError::Transaction(err) => Some(err),
            _ => None,
        }
    }

    /// Discard the error if it is a transaction error, returning the EVM. If
    /// the error is not a transaction error, return self
    pub fn discard_transaction_error(self) -> Result<EvmNeedsTx<Db, Insp>, Self> {
        if self.is_transaction_error() {
            Ok(self.discard_error())
        } else {
            Err(self)
        }
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
