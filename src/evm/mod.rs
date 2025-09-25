mod builder;
pub use builder::{TrevmBuilder, TrevmBuilderError};

mod factory;
pub use factory::EvmFactory;

pub(crate) mod states;

mod r#struct;
pub use r#struct::Trevm;

// Impl blocks for Evm states
mod all_states;
mod errored;
mod has_block;
mod has_cfg;
mod has_tx;
mod need_block;
mod need_cfg;
mod need_tx;
mod ready;
mod transacted;
