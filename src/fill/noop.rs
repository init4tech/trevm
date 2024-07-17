use revm::primitives::{BlockEnv, CfgEnv};

use crate::{Block, Cfg};

/// A no-op block filler.
#[derive(Debug)]
pub struct NoopBlock;

impl Block for NoopBlock {
    fn fill_block_env(&self, _: &mut BlockEnv) {}
}

/// A no-op configuration filler.
#[derive(Debug)]
pub struct NoopCfg;

impl Cfg for NoopCfg {
    fn fill_cfg_env(&self, _: &mut CfgEnv) {}
}
