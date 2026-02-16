use crate::journal::{BundleStateIndex, JournalDecode, JournalDecodeError, JournalEncode};
use alloy::primitives::{keccak256, Bytes, B256};
use std::sync::OnceLock;

/// Journal associated with a block
#[derive(Debug, Clone)]
pub struct BlockUpdate<'a> {
    /// The height of the block.
    height: u64,

    /// The previous journal hash.
    prev_journal_hash: B256,

    /// The indexed changes.
    journal: BundleStateIndex<'a>,

    /// The serialized journal
    serialized: OnceLock<Bytes>,

    /// The hash of the serialized journal
    hash: OnceLock<B256>,
}

impl<'a> BlockUpdate<'a> {
    /// Create a new block update.
    pub const fn new(height: u64, prev_journal_hash: B256, journal: BundleStateIndex<'a>) -> Self {
        Self {
            height,
            prev_journal_hash,
            journal,
            serialized: OnceLock::new(),
            hash: OnceLock::new(),
        }
    }

    /// Get the height of the block.
    pub const fn height(&self) -> u64 {
        self.height
    }

    /// Get the previous journal hash.
    pub const fn prev_journal_hash(&self) -> B256 {
        self.prev_journal_hash
    }

    /// Get the journal index.
    pub const fn journal(&self) -> &BundleStateIndex<'a> {
        &self.journal
    }

    /// Decompose the block update into its parts.
    pub fn into_parts(self) -> (u64, B256, BundleStateIndex<'a>) {
        (self.height, self.prev_journal_hash, self.journal)
    }

    /// Serialize the block update.
    pub fn serialized(&self) -> &[u8] {
        self.serialized.get_or_init(|| JournalEncode::encoded(self)).as_ref()
    }

    /// Serialize and hash the block update.
    pub fn journal_hash(&self) -> B256 {
        *self.hash.get_or_init(|| keccak256(self.serialized()))
    }
}

impl JournalEncode for BlockUpdate<'_> {
    fn serialized_size(&self) -> usize {
        8 + 32 + self.journal.serialized_size()
    }

    fn encode(&self, buf: &mut dyn alloy::rlp::BufMut) {
        self.height.encode(buf);
        self.prev_journal_hash.encode(buf);
        self.journal.encode(buf);
    }
}

impl JournalDecode for BlockUpdate<'static> {
    fn decode(buf: &mut &[u8]) -> Result<Self, JournalDecodeError> {
        let original = *buf;
        let height = JournalDecode::decode(buf)?;
        let prev_journal_hash = JournalDecode::decode(buf)?;
        let journal = JournalDecode::decode(buf)?;

        let bytes_read = original.len() - buf.len();
        let original = &original[..bytes_read];

        Ok(Self {
            height,
            prev_journal_hash,
            journal,
            serialized: OnceLock::from(Bytes::copy_from_slice(original)),
            hash: OnceLock::from(keccak256(original)),
        })
    }
}

impl PartialEq for BlockUpdate<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self.hash.get(), other.hash.get()) {
            (Some(lhs), Some(rhs)) => lhs == rhs,
            _ => {
                self.height == other.height
                    && self.prev_journal_hash == other.prev_journal_hash
                    && self.journal == other.journal
            }
        }
    }
}

impl Eq for BlockUpdate<'_> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn block_update_eq_with_one_populated_hash() {
        let update_a = BlockUpdate::new(1, B256::ZERO, BundleStateIndex::default());
        let update_b = BlockUpdate::new(1, B256::ZERO, BundleStateIndex::default());
        update_a.journal_hash();
        assert!(update_a.hash.get().is_some());
        assert!(update_b.hash.get().is_none());
        assert_eq!(update_a, update_b);
    }
}
