use crate::journal::{AcctDiff, BundleStateIndex, InfoOutcome};
use alloy_primitives::{Address, Bytes, B256, U256};
use alloy_rlp::{Buf, BufMut};
use revm::{
    db::{states::StorageSlot, BundleState},
    primitives::{
        eof::EofDecodeError, AccountInfo, Bytecode, Eip7702Bytecode, Eip7702DecodeError, Eof,
    },
};
use std::{borrow::Cow, collections::BTreeMap, fmt::Debug, sync::Arc};
use zenith_types::Zenith;

type Result<T, E = JournalDecodeError> = std::result::Result<T, E>;

// Account Diff encoding
const TAG_ACCT_CREATED: u8 = 0;
const TAG_ACCT_DIFF: u8 = 1;
const TAG_ACCT_DESTROYED: u8 = 2;

// Storage Diff encoding
const TAG_STORAGE_DELETED: u8 = 0;
const TAG_STORAGE_CREATED: u8 = 1;
const TAG_STORAGE_CHANGED: u8 = 2;
const TAG_STORAGE_UNCHANGED: u8 = 3;

// Bytecode encoding
const TAG_BYTECODE_RAW: u8 = 0;
const TAG_BYTECODE_EOF: u8 = 1;
const TAG_BYTECODE_7702: u8 = 2;

// Option encoding
const TAG_OPTION_NONE: u8 = 0;
const TAG_OPTION_SOME: u8 = 1;

// Sizes
const ZENITH_HEADER_BYTES: usize = 32 + 32 + 32 + 20 + 32;
const ACCOUNT_INFO_BYTES: usize = 8 + 32 + 32;
const INFO_OUTCOME_MIN_BYTES: usize = 1 + ACCOUNT_INFO_BYTES;
const ACCT_DIFF_MIN_BYTES: usize = 4 + INFO_OUTCOME_MIN_BYTES;

/// Error decoding journal types.
#[derive(thiserror::Error, Debug, Copy, Clone, PartialEq, Eq)]
pub enum JournalDecodeError {
    /// The buffer does not contain enough data to decode the type.
    #[error("buffer overrun while decoding {ty_name}. Expected {expected} bytes, but only {remaining} bytes remain")]
    Overrun {
        /// The name of the type being decoded.
        ty_name: &'static str,
        /// The number of bytes required to decode the type.
        expected: usize,
        /// The number of bytes remaining in the buffer.
        remaining: usize,
    },

    /// Invalid tag while decoding a type.
    #[error("invalid tag while decoding {ty_name}. Expected a tag in range 0..={max_expected}, got {tag}")]
    InvalidTag {
        /// The name of the type being decoded.
        ty_name: &'static str,
        /// The tag that was decoded.
        tag: u8,
        /// The maximum expected tag value.
        max_expected: u8,
    },

    /// Storage slot is unchanged, journal should not contain unchanged slots.
    #[error("storage slot is unchanged. Unchanged items should never be in the journal")]
    UnchangedStorage,

    /// Error decoding an EOF bytecode.
    #[error("error decoding EOF bytecode: {0}")]
    EofDecode(#[from] EofDecodeError),

    /// Error decoding an EIP-7702 bytecode.
    #[error("error decoding EIP-7702 bytecode: {0}")]
    Eip7702Decode(#[from] Eip7702DecodeError),
}

macro_rules! check_len {
    ($buf:ident, $ty_name:literal, $len:expr) => {
        let rem = $buf.remaining();
        if rem < $len {
            return Err(JournalDecodeError::Overrun {
                ty_name: $ty_name,
                expected: $len,
                remaining: rem,
            });
        }
    };
}

/// Trait for encoding journal types to a buffer.
pub trait JournalEncode: Debug {
    /// Return the serialized size of the type, in bytes.
    fn serialized_size(&self) -> usize;

    /// Encode the type into the buffer.
    fn encode(&self, buf: &mut dyn BufMut);

    /// Shortcut to encode the type into a new vec.
    fn encoded(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.encode(&mut buf);
        buf
    }
}

impl<T> JournalEncode for Cow<'_, T>
where
    T: JournalEncode + ToOwned,
    T::Owned: Debug,
{
    fn serialized_size(&self) -> usize {
        self.as_ref().serialized_size()
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        self.as_ref().encode(buf);
    }
}

impl<T> JournalEncode for Option<T>
where
    T: JournalEncode,
{
    fn serialized_size(&self) -> usize {
        self.as_ref().map(|v| 1 + v.serialized_size()).unwrap_or(1)
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        match self {
            Some(value) => {
                buf.put_u8(TAG_OPTION_SOME);
                value.encode(buf);
            }
            None => {
                buf.put_u8(TAG_OPTION_NONE);
            }
        }
    }
}

impl JournalEncode for u8 {
    fn serialized_size(&self) -> usize {
        1
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        buf.put_u8(*self);
    }
}

impl JournalEncode for u32 {
    fn serialized_size(&self) -> usize {
        4
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        buf.put_u32(*self);
    }
}

impl JournalEncode for u64 {
    fn serialized_size(&self) -> usize {
        8
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        buf.put_u64(*self);
    }
}

impl JournalEncode for B256 {
    fn serialized_size(&self) -> usize {
        32
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        buf.put_slice(&self.0);
    }
}

impl JournalEncode for Address {
    fn serialized_size(&self) -> usize {
        20
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        buf.put_slice(self.0.as_ref());
    }
}

impl JournalEncode for U256 {
    fn serialized_size(&self) -> usize {
        32
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        buf.put_slice(&self.to_be_bytes::<32>());
    }
}

impl JournalEncode for AccountInfo {
    fn serialized_size(&self) -> usize {
        32 + 8 + 32
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        self.balance.encode(buf);
        self.nonce.encode(buf);
        self.code_hash.encode(buf);
    }
}

impl JournalEncode for InfoOutcome<'_> {
    fn serialized_size(&self) -> usize {
        // tag + 32 per account
        match self {
            Self::Diff { .. } => 1 + (32 + 8 + 32) * 2,
            _ => 1 + (32 + 8 + 32),
        }
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        match self {
            Self::Created(info) => {
                buf.put_u8(TAG_ACCT_CREATED);
                info.as_ref().encode(buf);
            }
            Self::Diff { old, new } => {
                buf.put_u8(TAG_ACCT_DIFF);
                old.as_ref().encode(buf);
                new.as_ref().encode(buf);
            }
            Self::Destroyed(old) => {
                buf.put_u8(TAG_ACCT_DESTROYED);
                old.as_ref().encode(buf);
            }
        }
    }
}

impl JournalEncode for StorageSlot {
    fn serialized_size(&self) -> usize {
        if self.original_value().is_zero() || self.present_value().is_zero() {
            // tag + 32 for present value
            33
        } else {
            // tag + 32 for present value + 32 for previous value
            1 + 32 + 32
        }
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        if !self.is_changed() {
            panic!("StorageSlot is unchanged. Unchanged items should never be in the journal. Enforced by filter in AcctDiff From impl, and in AcctDiff JournalEncode impl.");
        } else if self.original_value().is_zero() {
            buf.put_u8(TAG_STORAGE_CREATED);
            self.present_value.encode(buf);
        } else if self.present_value().is_zero() {
            buf.put_u8(TAG_STORAGE_DELETED);
            self.original_value().encode(buf);
        } else {
            buf.put_u8(TAG_STORAGE_CHANGED);
            // DO NOT REORDER
            self.present_value.encode(buf);
            self.previous_or_original_value.encode(buf);
        }
    }
}

impl JournalEncode for AcctDiff<'_> {
    fn serialized_size(&self) -> usize {
        // outcome size + u32 for storage diff len + storage diff size
        self.outcome.serialized_size()
            + 4
            + self
                .storage_diff
                .values()
                .filter(|s| s.is_changed())
                .fold(0, |acc, v| acc + 32 + v.serialized_size())
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        self.outcome.encode(buf);
        buf.put_u32(self.storage_diff.len() as u32);
        for (slot, value) in &self.storage_diff {
            if value.is_changed() {
                slot.encode(buf);
                value.encode(buf);
            }
        }
    }
}

impl JournalEncode for Bytecode {
    fn serialized_size(&self) -> usize {
        // tag + u32 for len + len of raw
        1 + 4 + self.bytes().len()
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        match self {
            Self::LegacyRaw(_) | Self::LegacyAnalyzed(_) => buf.put_u8(TAG_BYTECODE_RAW),
            Self::Eof(_) => buf.put_u8(TAG_BYTECODE_EOF),
            Self::Eip7702(_) => buf.put_u8(TAG_BYTECODE_7702),
        }

        let raw = self.bytes();
        buf.put_u32(raw.len() as u32);
        buf.put_slice(raw.as_ref());
    }
}

impl JournalEncode for BundleStateIndex<'_> {
    fn serialized_size(&self) -> usize {
        // u32 for len
        4
        // 20 for key, then size of value
        + self.state.values().fold(0, |acc, v|
            acc + 20 + v.serialized_size())
        // u32 for len of contracts
        + 4
        // 32 for key, then size of value
        + self.new_contracts.values().fold(0, |acc, v|
            acc + 32 + v.serialized_size()
        )
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        buf.put_u32(self.state.len() as u32);
        for (address, diff) in &self.state {
            address.encode(buf);
            diff.encode(buf);
        }
        buf.put_u32(self.new_contracts.len() as u32);
        for (code_hash, code) in &self.new_contracts {
            code_hash.encode(buf);
            code.encode(buf);
        }
    }
}

impl JournalEncode for BundleState {
    fn serialized_size(&self) -> usize {
        BundleStateIndex::from(self).serialized_size()
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        BundleStateIndex::from(self).encode(buf);
    }
}

impl JournalEncode for Zenith::BlockHeader {
    fn serialized_size(&self) -> usize {
        ZENITH_HEADER_BYTES
    }

    fn encode(&self, buf: &mut dyn BufMut) {
        let Self { rollupChainId, hostBlockNumber, gasLimit, rewardAddress, blockDataHash } = self;

        rollupChainId.encode(buf);
        hostBlockNumber.encode(buf);
        gasLimit.encode(buf);
        rewardAddress.encode(buf);
        blockDataHash.encode(buf);
    }
}

/// Trait for decoding journal types from a buffer.
pub trait JournalDecode: JournalEncode + Sized + 'static {
    /// Decode the type from the buffer.
    fn decode(buf: &mut &[u8]) -> Result<Self>;
}

impl<T> JournalDecode for Cow<'static, T>
where
    T: JournalEncode + ToOwned,
    T::Owned: JournalEncode + JournalDecode,
{
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        JournalDecode::decode(buf).map(Cow::Owned)
    }
}

impl<T> JournalDecode for Option<T>
where
    T: JournalDecode,
{
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        let tag: u8 = JournalDecode::decode(buf)?;
        match tag {
            TAG_OPTION_NONE => Ok(None),
            TAG_OPTION_SOME => Ok(Some(JournalDecode::decode(buf)?)),
            _ => Err(JournalDecodeError::InvalidTag { ty_name: "Option<T>", tag, max_expected: 1 }),
        }
    }
}

impl JournalDecode for u8 {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        check_len!(buf, "u8", 1);

        Ok(buf.get_u8())
    }
}

impl JournalDecode for u32 {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        check_len!(buf, "u32", 4);

        Ok(buf.get_u32())
    }
}

impl JournalDecode for u64 {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        check_len!(buf, "u64", 8);

        Ok(buf.get_u64())
    }
}

impl JournalDecode for B256 {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        check_len!(buf, "B256", 32);

        let mut b = Self::default();
        buf.copy_to_slice(b.as_mut());
        Ok(b)
    }
}

impl JournalDecode for Address {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        check_len!(buf, "Address", 20);

        let mut a = Self::default();
        buf.copy_to_slice(a.as_mut());
        Ok(a)
    }
}

impl JournalDecode for U256 {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        check_len!(buf, "U256", 32);

        let mut bytes = [0u8; 32];
        buf.copy_to_slice(&mut bytes);
        Ok(Self::from_be_bytes(bytes))
    }
}

impl JournalDecode for AccountInfo {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        check_len!(buf, "AccountInfo", ACCOUNT_INFO_BYTES);

        Ok(Self {
            balance: JournalDecode::decode(buf)?,
            nonce: JournalDecode::decode(buf)?,
            code_hash: JournalDecode::decode(buf)?,
            code: None,
        })
    }
}

impl JournalDecode for InfoOutcome<'static> {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        let tag = JournalDecode::decode(buf)?;

        match tag {
            TAG_ACCT_CREATED => {
                let info = JournalDecode::decode(buf)?;
                Ok(Self::Created(Cow::Owned(info)))
            }
            TAG_ACCT_DIFF => {
                let old = JournalDecode::decode(buf)?;
                let new = JournalDecode::decode(buf)?;
                Ok(Self::Diff { old: Cow::Owned(old), new: Cow::Owned(new) })
            }
            TAG_ACCT_DESTROYED => {
                let info = JournalDecode::decode(buf)?;
                Ok(Self::Destroyed(Cow::Owned(info)))
            }
            _ => {
                Err(JournalDecodeError::InvalidTag { ty_name: "InfoOutcome", tag, max_expected: 2 })
            }
        }
    }
}

impl JournalDecode for StorageSlot {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        let tag = JournalDecode::decode(buf)?;

        let present_value = JournalDecode::decode(buf)?;

        match tag {
            TAG_STORAGE_DELETED => Ok(Self::new_changed(present_value, U256::ZERO)),
            TAG_STORAGE_CREATED => Ok(Self::new_changed(U256::ZERO, present_value)),
            TAG_STORAGE_CHANGED => {
                let previous_or_original_value = JournalDecode::decode(buf)?;
                Ok(Self::new_changed(previous_or_original_value, present_value))
            }
            TAG_STORAGE_UNCHANGED => Err(JournalDecodeError::UnchangedStorage),
            _ => {
                Err(JournalDecodeError::InvalidTag { ty_name: "StorageSlot", tag, max_expected: 3 })
            }
        }
    }
}

impl JournalDecode for AcctDiff<'static> {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        let outcome = JournalDecode::decode(buf)?;

        check_len!(buf, "StorageDiffLen", ACCT_DIFF_MIN_BYTES);
        let storage_diff_len: u32 = JournalDecode::decode(buf)?;

        let mut storage_diff = BTreeMap::new();
        for _ in 0..storage_diff_len {
            let slot = JournalDecode::decode(buf)?;
            let value = JournalDecode::decode(buf)?;
            storage_diff.insert(slot, Cow::Owned(value));
        }

        Ok(AcctDiff { outcome, storage_diff })
    }
}

impl JournalDecode for Bytecode {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        let tag = JournalDecode::decode(buf)?;
        let len: u32 = JournalDecode::decode(buf)?;
        check_len!(buf, "BytecodeBody", len as usize);

        let raw: Bytes = buf.copy_to_bytes(len as usize).into();

        match tag {
            TAG_BYTECODE_RAW => Ok(Self::new_raw(raw)),
            TAG_BYTECODE_EOF => Ok(Self::Eof(Arc::new(Eof::decode(raw)?))),
            TAG_BYTECODE_7702 => Ok(Self::Eip7702(Eip7702Bytecode::new_raw(raw)?)),
            _ => Err(JournalDecodeError::InvalidTag { ty_name: "Bytecode", tag, max_expected: 2 }),
        }
    }
}

impl JournalDecode for BundleStateIndex<'static> {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        let state_len: u32 = JournalDecode::decode(buf)?;
        let mut state = BTreeMap::new();
        for _ in 0..state_len {
            let address = JournalDecode::decode(buf)?;
            let diff = JournalDecode::decode(buf)?;
            state.insert(address, diff);
        }

        let new_contracts_len: u32 = JournalDecode::decode(buf)?;
        let mut new_contracts = BTreeMap::new();
        for _ in 0..new_contracts_len {
            let address = JournalDecode::decode(buf)?;
            let code = JournalDecode::decode(buf)?;
            new_contracts.insert(address, Cow::Owned(code));
        }

        Ok(BundleStateIndex { state, new_contracts })
    }
}

impl JournalDecode for BundleState {
    // TODO(perf): we can manually implemnt the decoding here in order to avoid
    // allocating the btrees in the index

    fn decode(buf: &mut &[u8]) -> Result<Self> {
        BundleStateIndex::decode(buf).map(Self::from)
    }
}

impl JournalDecode for Zenith::BlockHeader {
    fn decode(buf: &mut &[u8]) -> Result<Self> {
        Ok(Self {
            rollupChainId: JournalDecode::decode(buf)?,
            hostBlockNumber: JournalDecode::decode(buf)?,
            gasLimit: JournalDecode::decode(buf)?,
            rewardAddress: JournalDecode::decode(buf)?,
            blockDataHash: JournalDecode::decode(buf)?,
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn roundtrip<T: JournalDecode + JournalEncode + PartialEq>(expected: &T) {
        let enc = JournalEncode::encoded(expected);
        assert_eq!(enc.len(), expected.serialized_size(), "{}", std::any::type_name::<T>());
        let dec = T::decode(&mut enc.as_slice()).expect("decoding failed");
        assert_eq!(&dec, expected);
    }

    #[test]
    fn roundtrips() {
        roundtrip(&Cow::<'static, u8>::Owned(1u8));
        roundtrip(&Cow::<'static, u32>::Owned(1u32));
        roundtrip(&Cow::<'static, u64>::Owned(1u64));
        roundtrip(&B256::repeat_byte(0xa));
        roundtrip(&Address::repeat_byte(0xa));
        roundtrip(&U256::from(38238923));

        let acc_info = AccountInfo {
            balance: U256::from(38238923),
            nonce: 38238923,
            code_hash: B256::repeat_byte(0xa),
            code: None,
        };
        roundtrip(&acc_info);
        let created_outcome = InfoOutcome::Created(Cow::Owned(acc_info));
        roundtrip(&created_outcome);

        let diff_outcome = InfoOutcome::Diff {
            old: Cow::Owned(AccountInfo {
                balance: U256::from(38),
                nonce: 38,
                code_hash: B256::repeat_byte(0xab),
                code: None,
            }),
            new: Cow::Owned(AccountInfo {
                balance: U256::from(38238923),
                nonce: 38238923,
                code_hash: B256::repeat_byte(0xa),
                code: None,
            }),
        };
        roundtrip(&diff_outcome);

        let new_slot = StorageSlot::new_changed(U256::ZERO, U256::from(38238923));
        let changed_slot = StorageSlot::new_changed(U256::from(38238923), U256::from(3));
        let deleted_slot = StorageSlot::new_changed(U256::from(17), U256::ZERO);

        roundtrip(&new_slot);
        roundtrip(&changed_slot);
        roundtrip(&deleted_slot);

        let created_acc = AcctDiff {
            outcome: created_outcome,
            storage_diff: vec![
                (U256::from(3), Cow::Owned(new_slot.clone())),
                (U256::from(4), Cow::Owned(changed_slot.clone())),
                (U256::from(5), Cow::Owned(deleted_slot.clone())),
            ]
            .into_iter()
            .collect(),
        };
        roundtrip(&created_acc);

        let changed_acc = AcctDiff {
            outcome: diff_outcome,
            storage_diff: vec![
                (U256::from(3), Cow::Owned(new_slot)),
                (U256::from(4), Cow::Owned(changed_slot)),
                (U256::from(5), Cow::Owned(deleted_slot)),
            ]
            .into_iter()
            .collect(),
        };
        roundtrip(&changed_acc);

        let bytecode = Bytecode::new_raw(Bytes::from(vec![1, 2, 3]));
        let eof_bytes = Bytecode::Eof(Arc::new(Eof::default()));
        roundtrip(&bytecode);
        roundtrip(&eof_bytes);

        let bsi = BundleStateIndex {
            state: vec![
                (Address::repeat_byte(0xa), created_acc),
                (Address::repeat_byte(0xb), changed_acc),
            ]
            .into_iter()
            .collect(),
            new_contracts: vec![
                (B256::repeat_byte(0xa), Cow::Owned(bytecode)),
                (B256::repeat_byte(0xb), Cow::Owned(eof_bytes)),
            ]
            .into_iter()
            .collect(),
        };
        roundtrip(&bsi);

        roundtrip(&Zenith::BlockHeader {
            rollupChainId: U256::from(1),
            hostBlockNumber: U256::from(1),
            gasLimit: U256::from(1),
            rewardAddress: Address::repeat_byte(0xa),
            blockDataHash: B256::repeat_byte(0xa),
        });
    }
}
