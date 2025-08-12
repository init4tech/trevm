use crate::journal::{BundleStateIndex, JournalDecode, JournalDecodeError, JournalEncode};
use alloy::primitives::{keccak256, B256};
use std::sync::OnceLock;

/// Journal associated with a block
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockUpdate<'a> {
    /// The height of the block.
    height: u64,

    /// The previous journal hash.
    prev_journal_hash: B256,

    /// The indexed changes.
    journal: BundleStateIndex<'a>,

    /// The serialized journal
    serialized: OnceLock<Vec<u8>>,

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

    /// Serialize the block update.
    pub fn serialized(&self) -> &[u8] {
        self.serialized.get_or_init(|| JournalEncode::encoded(self)).as_slice()
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
        Ok(Self {
            height: JournalDecode::decode(buf)?,
            prev_journal_hash: JournalDecode::decode(buf)?,
            journal: JournalDecode::decode(buf)?,
            serialized: OnceLock::from(original.to_vec()),
            hash: OnceLock::from(keccak256(original)),
        })
    }
}
