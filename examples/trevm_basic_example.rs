//! Basic Trevm example demonstrating safe transaction execution

use revm::database::InMemoryDB;
use revm::{
    context::TxEnv,
    primitives::{hex, Address, TxKind},
};
use trevm::{NoopBlock, NoopCfg, TrevmBuilder, Tx};

struct MyTransaction {
    caller: Address,
    to: Address,
    data: Vec<u8>,
}

impl Tx for MyTransaction {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        tx_env.caller = self.caller;
        tx_env.kind = TxKind::Call(self.to);
        tx_env.data = self.data.clone().into();
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Trevm provides safe, guided workflow
    let tx = MyTransaction {
        caller: Address::with_last_byte(1),
        to: Address::with_last_byte(2),
        data: hex::decode("deadbeef")?,
    };

    // Type-safe builder pattern
    let result = TrevmBuilder::new()
        .with_db(InMemoryDB::default())
        .build_trevm()? // EvmNeedsCfg
        .fill_cfg(&NoopCfg) // EvmNeedsBlock
        .fill_block(&NoopBlock) // EvmNeedsTx
        .run_tx(&tx); // Result<EvmTransacted, EvmErrored>

    // Safe error handling with type guarantees
    match result {
        Ok(transacted) => {
            println!("Transaction succeeded!");
            let _final_evm = transacted.accept_state(); // EvmNeedsTx
                                                        // State automatically applied
        }
        Err(errored) => {
            println!("Transaction failed: {:?}", errored.error());
            let _recovered_evm = errored.discard_error(); // EvmNeedsTx
                                                          // Can continue with next transaction
        }
    }

    Ok(())
}
