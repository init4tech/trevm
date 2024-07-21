//! Simple TREVM example that demonstrates how to execute a transaction on a contract.
//! It simply loads the contract bytecode and executes a transaction.

use revm::{
    db::{CacheDB, EmptyDB},
    inspector_handle_register,
    inspectors::TracerEip3155,
    primitives::{hex, AccountInfo, Address, Bytecode, TransactTo, U256},
    EvmBuilder,
};
use trevm::{Block, Cfg, ShanghaiLifecycle, TrevmBuilder, Tx};

/// Foundry's default Counter.sol contract bytecode.
const CONTRACT_BYTECODE: &str = "0x6080604052348015600f57600080fd5b5060043610603c5760003560e01c80633fb5c1cb1460415780638381f58a146053578063d09de08a14606d575b600080fd5b6051604c3660046083565b600055565b005b605b60005481565b60405190815260200160405180910390f35b6051600080549080607c83609b565b9190505550565b600060208284031215609457600080fd5b5035919050565b60006001820160ba57634e487b7160e01b600052601160045260246000fd5b506001019056fea2646970667358221220091e48831e9eee32d4571d6291233a4fdaaa34b7dced8770f36f5368be825c5264736f6c63430008190033";

/// The address of Counter.sol
const CONTRACT_ADDR: Address = Address::with_last_byte(32);

/// The input data for the Counter.sol program. We're calling setNumber(10)
const PROGRAM_INPUT: &str =
    "0x3fb5c1cb000000000000000000000000000000000000000000000000000000000000000a";

/// The caller address
const CALLER_ADDR: Address = Address::with_last_byte(1);

struct NoopCfg;
struct NoopBlock;
struct SampleTx;

impl Cfg for NoopCfg {
    fn fill_cfg_env(&self, _: &mut revm::primitives::CfgEnv) {}
}

impl Block for NoopBlock {
    fn fill_block_env(&self, _: &mut revm::primitives::BlockEnv) {}
}

impl Tx for SampleTx {
    fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
        tx_env.caller = CALLER_ADDR;
        tx_env.transact_to = TransactTo::Call(CONTRACT_ADDR);
        tx_env.data = hex::decode(PROGRAM_INPUT).unwrap().into();
    }
}

fn main() {
    let mut db = CacheDB::new(EmptyDB::new());

    let bytecode = Bytecode::new_raw(hex::decode(CONTRACT_BYTECODE).unwrap().into());
    let acc_info = AccountInfo::new(U256::ZERO, 1, bytecode.hash_slow(), bytecode);

    // insert both the contract code to the contract cache, and the account info to the account cache
    db.insert_contract(&mut acc_info.clone());
    db.insert_account_info(CONTRACT_ADDR, acc_info);

    let evm = EvmBuilder::default()
        .with_db(db)
        .with_external_context(TracerEip3155::new(Box::new(std::io::stdout())))
        .append_handler_register(inspector_handle_register)
        .build_trevm();

    let account = evm.read_account_ref(CONTRACT_ADDR).unwrap();

    println!("account: {account:?}");

    let evm = evm.fill_cfg(&NoopCfg);

    let evm = evm.open_block(&NoopBlock, &mut ShanghaiLifecycle::default()).unwrap();

    let evm = evm.fill_tx(&SampleTx).execute_tx();

    match evm {
        Ok(res) => {
            let res = res.result_and_state();
            println!("Execution result: {res:#?}");
        }
        Err(e) => {
            println!("Execution error: {e:?}");
        }
    };
}
