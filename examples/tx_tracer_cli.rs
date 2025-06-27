//! CLI tool for tracing Ethereum transactions using Trevm
//!
//! Usage: cargo run --example tx_tracer_cli
//!
//! This tool demonstrates transaction tracing with detailed EVM execution logs.

use revm::{
    context::{BlockEnv, TxEnv},
    database::InMemoryDB,
    inspector::inspectors::TracerEip3155,
    primitives::{Address, TxKind, U256},
    state::AccountInfo,
};
use std::env;
use trevm::{trevm_aliases, Block, NoopCfg, TrevmBuilder, Tx};

// Type aliases for our specific setup
trevm_aliases!(InMemoryDB, TracerEip3155);

struct TracedTransaction {
    tx_env: TxEnv,
}

impl Tx for TracedTransaction {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        *tx_env = self.tx_env.clone();
    }
}

struct TracedBlock {
    block_env: BlockEnv,
}

impl Block for TracedBlock {
    fn fill_block_env(&self, block_env: &mut BlockEnv) {
        *block_env = self.block_env.clone();
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();

    println!("🔍 Trevm Transaction Tracer");
    println!("This example demonstrates EVM transaction tracing");

    // Setup database with pre-funded accounts
    let mut db = InMemoryDB::default();

    let caller = Address::with_last_byte(1);
    let contract_addr = Address::with_last_byte(2);

    // Fund the caller account
    let caller_info = AccountInfo::new(
        U256::from(1_000_000_000_000_000_000u64), // 1 ETH
        0,
        Default::default(),
        Default::default(),
    );
    db.insert_account_info(caller, caller_info);

    // Create tracer for detailed output
    let tracer = TracerEip3155::new(Box::new(std::io::stdout()));

    // Example 1: Contract deployment
    let deploy_bytecode = hex::decode("608060405234801561001057600080fd5b50600a600081905550")?;

    let deploy_tx_env = TxEnv {
        caller,
        kind: TxKind::Create,
        data: deploy_bytecode.into(),
        gas_limit: 500_000,
        gas_price: 1_000_000_000, // 1 gwei (must be >= basefee)
        nonce: 0,
        ..Default::default()
    };

    let deploy_tx = TracedTransaction { tx_env: deploy_tx_env };

    // Prepare block environment
    let block_env = BlockEnv {
        number: U256::from(1u64),
        timestamp: U256::from(1234567890u64),
        gas_limit: 30_000_000,
        basefee: 1_000_000_000, // 1 gwei
        beneficiary: Address::with_last_byte(255),
        ..Default::default()
    };

    let traced_block = TracedBlock { block_env };

    println!("\n🚀 Tracing contract deployment...");
    println!("{}", "=".repeat(80));

    // Execute contract deployment with tracing
    let result = TrevmBuilder::new()
        .with_db(db)
        .with_insp(tracer)
        .build_trevm()?
        .fill_cfg(&NoopCfg)
        .fill_block(&traced_block)
        .run_tx(&deploy_tx);

    println!("{}", "=".repeat(80));

    match result {
        Ok(transacted) => {
            let execution_result = transacted.result();
            println!("✅ Contract deployment executed!");
            println!("📊 Execution Summary:");
            println!("   Gas Used: {}", execution_result.gas_used());
            println!("   Success: {}", execution_result.is_success());

            if let Some(output) = transacted.output() {
                println!("   Output: 0x{}", hex::encode(output));
            }

            // For contract creation, check if it was successful
            if matches!(deploy_tx.tx_env.kind, TxKind::Create) && execution_result.is_success() {
                println!("   ✨ Contract deployed successfully!");
            }

            // Show state changes
            let state_changes = transacted.state();
            if !state_changes.is_empty() {
                println!("\n🔄 State Changes:");
                for (addr, account) in state_changes.iter() {
                    println!("   Account: {:?}", addr);
                    println!("     Balance: {}", account.info.balance);
                    println!("     Nonce: {}", account.info.nonce);
                    if !account.storage.is_empty() {
                        println!("     Storage changes: {}", account.storage.len());
                    }
                }
            }

            println!("\n✨ Transaction tracing completed successfully!");

            // Example 2: Simple transfer (if you want to see a simpler trace)
            if args.len() > 1 && args[1] == "--transfer" {
                println!("\n🔄 Tracing simple transfer...");
                println!("{}", "=".repeat(80));

                let transfer_tx_env = TxEnv {
                    caller,
                    kind: TxKind::Call(contract_addr),
                    value: U256::from(100_000_000_000_000_000u64), // 0.1 ETH
                    data: vec![].into(),                           // No data for simple transfer
                    gas_limit: 21_000,
                    gas_price: 1_000_000_000, // 1 gwei (must be >= basefee)
                    nonce: 1,                 // Increment nonce for the transfer
                    ..Default::default()
                };

                let transfer_tx = TracedTransaction { tx_env: transfer_tx_env };

                // Get the EVM back for the next transaction
                let evm = transacted.accept_state();

                // Create a new tracer for the transfer
                let transfer_tracer = TracerEip3155::new(Box::new(std::io::stdout()));

                let transfer_result = TrevmBuilder::new()
                    .with_db(evm.into_db())
                    .with_insp(transfer_tracer)
                    .build_trevm()?
                    .fill_cfg(&NoopCfg)
                    .fill_block(&traced_block)
                    .run_tx(&transfer_tx);

                println!("{}", "=".repeat(80));

                match transfer_result {
                    Ok(transfer_transacted) => {
                        println!("✅ Transfer executed!");
                        println!("   Gas Used: {}", transfer_transacted.gas_used());
                    }
                    Err(transfer_errored) => {
                        println!("❌ Transfer failed: {:?}", transfer_errored.error());
                    }
                }
            }
        }
        Err(errored) => {
            println!("❌ Transaction execution failed!");
            println!("Error: {:?}", errored.error());
        }
    }

    println!("\n💡 Tips:");
    println!("   - Run with --transfer to see a simple transfer trace");
    println!("   - The trace shows each EVM opcode execution step");
    println!("   - Gas costs and stack/memory changes are displayed");

    Ok(())
}

// Helper to make hex encoding/decoding available
mod hex {
    pub(crate) fn encode(data: &[u8]) -> String {
        data.iter().map(|b| format!("{:02x}", b)).collect()
    }

    pub(crate) fn decode(s: &str) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let s = s.strip_prefix("0x").map_or(s, |s| &s[2..]);
        if s.len() % 2 != 0 {
            return Err("Invalid hex string length".into());
        }

        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|e| e.into()))
            .collect()
    }
}
