//! Block driver example showing how to process multiple transactions

use revm::{
    database::InMemoryDB,
    inspector::NoOpInspector,
    primitives::{Address, TxKind, U256},
    context::{TxEnv, BlockEnv},
    state::AccountInfo,
};
use trevm::{
    BlockDriver, RunTxResult, NoopCfg, TrevmBuilder, Tx, Block,
    trevm_aliases
};

trevm_aliases!(InMemoryDB);

struct SimpleTransfer {
    from: Address,
    to: Address,
    value: U256,
    nonce: u64,
}

impl Tx for SimpleTransfer {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        tx_env.caller = self.from;
        tx_env.kind = TxKind::Call(self.to);
        tx_env.value = self.value;
        tx_env.gas_limit = 21_000;
        tx_env.nonce = self.nonce;
    }
}

struct SimpleBlock {
    number: u64,
    timestamp: u64,
}

impl Block for SimpleBlock {
    fn fill_block_env(&self, block_env: &mut BlockEnv) {
        block_env.number = self.number;
        block_env.timestamp = self.timestamp;
        block_env.gas_limit = 30_000_000u64; // 30M gas limit
    }
}

#[derive(Debug)]
struct SimpleDriverError(String);

impl std::fmt::Display for SimpleDriverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SimpleDriverError: {}", self.0)
    }
}

impl std::error::Error for SimpleDriverError {}

impl From<revm::context::result::EVMError<std::convert::Infallible>> for SimpleDriverError {
    fn from(err: revm::context::result::EVMError<std::convert::Infallible>) -> Self {
        SimpleDriverError(format!("EVM Error: {:?}", err))
    }
}

struct SimpleBlockDriver {
    transactions: Vec<SimpleTransfer>,
    block: SimpleBlock,
}

impl SimpleBlockDriver {
    fn new(transactions: Vec<SimpleTransfer>, block_number: u64) -> Self {
        Self {
            transactions,
            block: SimpleBlock {
                number: block_number,
                timestamp: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
            },
        }
    }
}

impl BlockDriver<InMemoryDB, NoOpInspector> for SimpleBlockDriver {
    type Block = SimpleBlock;
    type Error = SimpleDriverError;
    
    fn block(&self) -> &Self::Block {
        &self.block
    }
    
    fn run_txns(&mut self, mut evm: trevm::EvmNeedsTx<InMemoryDB, NoOpInspector>) -> RunTxResult<Self, InMemoryDB, NoOpInspector> {
        println!("Processing {} transactions", self.transactions.len());
        
        for (i, tx) in self.transactions.iter().enumerate() {
            println!("Processing transaction {}", i + 1);
            
            match evm.run_tx(tx) {
                Ok(transacted) => {
                    let gas_used = transacted.gas_used();
                    evm = transacted.accept_state();
                    println!("Transaction {} succeeded, gas used: {}", i + 1, gas_used);
                }
                Err(errored) => {
                    println!("Transaction {} failed: {:?}", i + 1, errored.error());
                    evm = errored.discard_error();
                    // Continue processing other transactions
                }
            }
        }
        
        Ok(evm)
    }
    
    fn post_block(&mut self, _evm: &trevm::EvmNeedsBlock<InMemoryDB, NoOpInspector>) -> Result<(), Self::Error> {
        println!("Post-block processing completed");
        println!("Processed {} transactions", self.transactions.len());
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut db = InMemoryDB::default();
    
    // Setup accounts
    let alice = Address::with_last_byte(1);
    let bob = Address::with_last_byte(2);
    let charlie = Address::with_last_byte(3);
    
    // Fund Alice
    let alice_info = AccountInfo::new(
        U256::from(1_000_000_000_000_000_000u64), // 1 ETH
        0,
        Default::default(),
        Default::default()
    );
    db.insert_account_info(alice, alice_info);
    
    // Create some transactions
    let transactions = vec![
        SimpleTransfer {
            from: alice,
            to: bob,
            value: U256::from(100_000_000_000_000_000u64), // 0.1 ETH
            nonce: 0,
        },
        SimpleTransfer {
            from: alice,
            to: charlie,
            value: U256::from(200_000_000_000_000_000u64), // 0.2 ETH
            nonce: 1,
        },
    ];
    
    let mut driver = SimpleBlockDriver::new(transactions, 1);
    
    // Use the driver to process the block
    let result = TrevmBuilder::new()
        .with_db(db)
        .build_trevm()?
        .fill_cfg(&NoopCfg)
        .drive_block(&mut driver);
    
    match result {
        Ok(_evm_needs_block) => {
            println!("Block processed successfully!");
        }
        Err(errored) => {
            println!("Block processing failed: {:?}", errored.error());
        }
    }
    
    Ok(())
}