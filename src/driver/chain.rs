use revm::{Database, DatabaseCommit};

pub trait ChainDriver<Ext, Db: Database + DatabaseCommit> {}
