use crate::syscall::SystemCall;
use alloy_primitives::{address, Address, Bytes, B256};

/// The address for the [EIP-4788] beacon roots contract.
///
/// [`EIP-4788`]: https://eips.ethereum.org/EIPS/eip-4788
pub const BEACON_ROOTS_ADDRESS: Address = address!("000F3df6D732807Ef1319fB7B8bB8522d0Beac02");

impl SystemCall {
    /// Instantiate a system call for the pre-block beacon roots as specified in
    /// [EIP-4788].
    ///
    /// [`EIP-4788`]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn eip4788(parent_beacon_root: B256) -> Self {
        Self::eip4788_with_target(parent_beacon_root, BEACON_ROOTS_ADDRESS)
    }

    /// Instantiate a system call for the pre-block beacon roots as specified in
    /// [EIP-4788], with a custom target address.
    ///
    /// [`EIP-4788`]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn eip4788_with_target(parent_beacon_root: B256, target: Address) -> Self {
        Self::new(target, Bytes::from(parent_beacon_root))
    }
}