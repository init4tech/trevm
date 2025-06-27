//! Advanced Trevm example with custom inspector for tracing

use revm::{
    context::result::{ExecutionResult, Output},
    context::TxEnv,
    database::InMemoryDB,
    inspector::inspectors::TracerEip3155,
    primitives::{hex, Address, TxKind, U256},
    state::AccountInfo,
};
use trevm::{trevm_aliases, NoopBlock, NoopCfg, TrevmBuilder, Tx};

// Create type aliases for cleaner code
trevm_aliases!(InMemoryDB, TracerEip3155);

struct DeployContract {
    caller: Address,
    bytecode: Vec<u8>,
}

impl Tx for DeployContract {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        tx_env.caller = self.caller;
        tx_env.kind = TxKind::Create;
        tx_env.data = self.bytecode.clone().into();
        tx_env.gas_limit = 500_000;
    }
}

struct CallContract {
    caller: Address,
    to: Address,
    data: Vec<u8>,
    nonce: u64,
}

impl Tx for CallContract {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        tx_env.caller = self.caller;
        tx_env.kind = TxKind::Call(self.to);
        tx_env.data = self.data.clone().into();
        tx_env.gas_limit = 100_000;
        tx_env.nonce = self.nonce;
    }
}

// Helper function to extract created contract address from ExecutionResult
const fn get_created_address(result: &ExecutionResult) -> Option<Address> {
    match result {
        ExecutionResult::Success { output: Output::Create(_bytes, address), .. } => *address,
        _ => None,
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut db = InMemoryDB::default();

    // Pre-fund deployer account
    let deployer = Address::with_last_byte(1);
    let acc_info = AccountInfo::new(
        U256::from(1_000_000_000_000_000_000u64),
        0,
        Default::default(),
        Default::default(),
    );
    db.insert_account_info(deployer, acc_info);

    // Create tracer that outputs to stdout
    let tracer = TracerEip3155::new(Box::new(std::io::stdout()));

    // Deploy contract with tracing
    let deploy_tx = DeployContract {
        caller: deployer,
        bytecode: hex::decode("608060405234801561001057600080fd5b50600a600081905550")?,
    };

    let mut evm: EvmNeedsTx = TrevmBuilder::new()
        .with_db(db)
        .with_insp(tracer)
        .build_trevm()?
        .fill_cfg(&NoopCfg)
        .fill_block(&NoopBlock);

    // Deploy contract
    println!("=== Deploying Contract ===");
    evm = match evm.run_tx(&deploy_tx) {
        Ok(transacted) => {
            println!("Contract deployed successfully!");
            if let Some(deployed_addr) = get_created_address(transacted.result()) {
                println!("Contract address: {:?}", deployed_addr);

                // Now call the contract
                let call_tx = CallContract {
                    caller: deployer,
                    to: deployed_addr,
                    data: vec![], // Simple call with no data
                    nonce: 1,     // Nonce after deployment transaction
                };

                println!("\n=== Calling Contract ===");
                let final_evm = transacted.accept_state();
                match final_evm.run_tx(&call_tx) {
                    Ok(call_result) => {
                        println!("Contract call succeeded!");
                        call_result.accept_state()
                    }
                    Err(call_error) => {
                        println!("Contract call failed: {:?}", call_error.error());
                        call_error.discard_error()
                    }
                }
            } else {
                transacted.accept_state()
            }
        }
        Err(deploy_error) => {
            println!("Contract deployment failed: {:?}", deploy_error.error());
            deploy_error.discard_error()
        }
    };

    // Close block and get final state
    let _final_evm = evm.close_block();
    println!("\nTransaction execution completed successfully!");

    Ok(())
}
