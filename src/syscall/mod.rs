//! Helpers for system actions including [EIP-4788], [EIP-6110], [EIP-7002] and
//! [EIP-7251].
//!
//! System actions are special state changes or smart contract calls made
//! before or after transaction exection. These actions are introduced via
//! hardfork. System actions are sometimes modeled as transactions with special
//! properties (as in [EIP-4788], [EIP-7002] and [EIP-7251]) or as special state
//! changes outside of the transaction lifecycle (as in [EIP-6110]).
//!
//! System transactions are modeled by the [`SystemTx`] struct, which implements
//! the [`Tx`] trait. The system transactions are sent from a special system
//! caller address: [`DEFAULT_SYSTEM_CALLER`]. Note that the system caller is
//! specified independently in each EIP, which allows introduction off
//! different system callers in future EIPs
//!
//! [`Tx`]: crate::Tx
//!
//! [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
//! [EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110
//! [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
//! [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251

mod fill;
pub use fill::{SystemTx, DEFAULT_SYSTEM_CALLER};

/// Helpers for Cancun beacon root [EIP-4788] system actions.
///
/// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
pub mod eip4788;

/// Helpers for Shanghai withdrawal [EIP-6110] system actions.
///
/// [EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110
pub mod eip6110;

/// Helpers for Prague withdrawal request [EIP-7002] system actions.
///
/// [EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002
pub mod eip7002;

/// Helpers for Prague consolidation request [EIP-7251] system actions.
///
/// [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
pub mod eip7251;
