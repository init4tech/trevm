//! Special transactions specified in EIPs [4788], [7002], and [7251].
//!
//!
//!
//! [4788]: https://eips.ethereum.org/EIPS/eip-4788
//! [7002]: https://eips.ethereum.org/EIPS/eip-7002
//! [7251]: https://eips.ethereum.org/EIPS/eip-7251

mod fill;
pub use fill::{SystemCall, DEFAULT_SYSTEM_CALLER};

mod eip4788;
pub use eip4788::BEACON_ROOTS_ADDRESS;

mod eip6110;
pub use eip6110::{parse_deposit_from_log, DepositEvent, MAINNET_DEPOSIT_ADDRESS};

mod eip7002;
pub use eip7002::{WITHDRAWAL_REQUEST_BYTES, WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS};

mod eip7251;
pub use eip7251::{CONSOLIDATION_REQUEST_BYTES, CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS};
