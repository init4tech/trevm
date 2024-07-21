use crate::syscall::SystemCall;
use alloy_primitives::{address, Address, Bytes};

/// The address for the [EIP-7002] withdrawal requests contract.
///
/// [`EIP-7002`]: https://eips.ethereum.org/EIPS/eip-7002
pub const WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS: Address =
    address!("00A3ca265EBcb825B45F985A16CEFB49958cE017");

/// The size of a withdrawal request in bytes.
pub const WITHDRAWAL_REQUEST_BYTES: usize = 20 + 48 + 8;

impl SystemCall {
    /// Instantiate a system call for the post-block withdrawal requests as
    /// specified in [EIP-7002].
    ///
    /// [`EIP-7002`]: https://eips.ethereum.org/EIPS/eip-7002
    pub const fn eip7002() -> Self {
        Self::eip7002_with_target(WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS)
    }

    /// Instantiate a system call for the post-block withdrawal requests as
    /// specified in [EIP-7002], with a custom target address.
    ///
    /// [`EIP-7002`]: https://eips.ethereum.org/EIPS/eip-7002
    pub const fn eip7002_with_target(target: Address) -> Self {
        Self::new(target, Bytes::new())
    }
}
