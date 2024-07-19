use crate::syscall::SystemCall;
use alloy_primitives::{address, Address, Bytes};

/// The address for the [EIP-7251] consolidation requests contract
///
/// [`EIP-7251`]: https://eips.ethereum.org/EIPS/eip-7251
pub const CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS: Address =
    address!("00b42dbF2194e931E80326D950320f7d9Dbeac02");

/// The size of a consolidation request in bytes.
pub const CONSOLIDATION_REQUEST_BYTES: usize = 20 + 48 + 48;

impl SystemCall {
    /// Instantiate a system call for the post-block consolidation requests as
    /// specified in [EIP-7251].
    ///
    /// [`EIP-7251`]: https://eips.ethereum.org/EIPS/eip-7251
    pub const fn eip7251() -> Self {
        Self::eip7251_with_target(CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS)
    }

    /// Instantiate a system call for the post-block consolidation requests as
    /// specified in [EIP-7251], with a custom target address.
    ///
    /// [`EIP-7251`]: https://eips.ethereum.org/EIPS/eip-7251
    pub const fn eip7251_with_target(target: Address) -> Self {
        Self::new(target, Bytes::new())
    }
}
