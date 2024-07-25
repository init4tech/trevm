use crate::syscall::SystemTx;
use alloy_primitives::{Address, Bytes, B256};

/// The address for the [EIP-4788] beacon roots contract.
///
/// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
pub use alloy_eips::eip4788::BEACON_ROOTS_ADDRESS;

impl SystemTx {
    /// Instantiate a system call for the pre-block beacon roots as specified in
    /// [EIP-4788].
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn eip4788(parent_beacon_root: B256) -> Self {
        Self::eip4788_with_target(parent_beacon_root, BEACON_ROOTS_ADDRESS)
    }

    /// Instantiate a system call for the pre-block beacon roots as specified in
    /// [EIP-4788], with a custom target address.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn eip4788_with_target(parent_beacon_root: B256, target: Address) -> Self {
        Self::new(target, Bytes::from(parent_beacon_root))
    }

    /// Instantiate a system call for the pre-block beacon roots as specified in
    /// [EIP-4788], with a custom target address and caller address.
    ///
    /// [EIP-4788]: https://eips.ethereum.org/EIPS/eip-4788
    pub fn eip4788_with_target_and_caller(
        parent_beacon_root: B256,
        target: Address,
        caller: Address,
    ) -> Self {
        Self::new_with_caller(target, Bytes::from(parent_beacon_root), caller)
    }
}
