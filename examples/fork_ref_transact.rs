//! This example demonstrates how to query storage slots of a contract, using AlloyDB.

use alloy_eips::BlockId;
use alloy_primitives::Address;
use alloy_provider::ProviderBuilder;
use alloy_sol_types::sol;
use alloy_sol_types::SolCall;
use revm::{
    db::{AlloyDB, CacheDB, EmptyDB},
    primitives::{address, ExecutionResult, TxKind, U256},
    Database, Evm,
};
use trevm::Block;
use trevm::Cfg;
use trevm::Shanghai;
use trevm::TrevmBuilder;
use trevm::Tx;

sol! {
    #[allow(missing_docs)]
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
}

struct NoopCfg;
struct NoopBlock;
struct GetReservesFiller;

impl Cfg for NoopCfg {
    fn fill_cfg_env(&self, _: &mut revm::primitives::CfgEnv) {}
}

impl Block for NoopBlock {
    fn fill_block_env(&self, _: &mut revm::primitives::BlockEnv) {}
}

impl Tx for GetReservesFiller {
    fn fill_tx_env(&self, tx_env: &mut revm::primitives::TxEnv) {
        tx_env.caller = Address::with_last_byte(0);
        // ETH/USDT pair on Uniswap V2
        tx_env.transact_to = TxKind::Call(POOL_ADDRESS);
        // calldata formed via alloy's abi encoder
        tx_env.data = getReservesCall::new(()).abi_encode().into();
        // transaction value in wei
        tx_env.value = U256::from(0);
    }
}

const POOL_ADDRESS: Address = address!("0d4a11d5EEaaC28EC3F61d100daF4d40471f1852");

#[tokio::main]
async fn main() -> eyre::Result<()> {
    // create ethers client and wrap it in Arc<M>
    let rpc_url = "https://mainnet.infura.io/v3/c60b0bb42f8a4c6481ecd229eddaca27";

    let client = ProviderBuilder::new().on_http(rpc_url.parse()?);

    // ----------------------------------------------------------- //
    //             Storage slots of UniV2Pair contract             //
    // =========================================================== //
    // storage[5] = factory: address                               //
    // storage[6] = token0: address                                //
    // storage[7] = token1: address                                //
    // storage[8] = (res0, res1, ts): (uint112, uint112, uint32)   //
    // storage[9] = price0CumulativeLast: uint256                  //
    // storage[10] = price1CumulativeLast: uint256                 //
    // storage[11] = kLast: uint256                                //
    // =========================================================== //

    // choose slot of storage that you would like to transact with
    let slot = U256::from(8);

    // initialize new AlloyDB
    let mut alloydb = AlloyDB::new(client, BlockId::default()).unwrap();

    // query basic properties of an account incl bytecode
    let acc_info = alloydb.basic(POOL_ADDRESS).unwrap().unwrap();

    // query value of storage slot at account address
    let value = alloydb.storage(POOL_ADDRESS, slot).unwrap();

    // initialise empty in-memory-db
    let mut cache_db = CacheDB::new(EmptyDB::default());

    // insert basic account info which was generated via Web3DB with the corresponding address
    cache_db.insert_account_info(POOL_ADDRESS, acc_info);

    // insert our pre-loaded storage slot to the corresponding contract key (address) in the DB
    cache_db.insert_account_storage(POOL_ADDRESS, slot, value).unwrap();

    // initialise an empty (default) EVM
    let evm = Evm::builder().with_db(cache_db).build_trevm();

    let evm = evm.fill_cfg(&NoopCfg);
    let evm = evm.open_block(&NoopBlock, &mut Shanghai::default()).unwrap();

    let evm = evm.fill_tx(&GetReservesFiller).execute_tx();

    let value = match evm {
        Ok(res) => {
            let exec_result = res.result();
            println!("Execution result: {:#?}", res.result());
            match exec_result {
                ExecutionResult::Success { output, .. } => output.to_owned(),
                _ => panic!("Execution failed"),
            }
        }
        Err(e) => {
            panic!("Execution error: {e:?}");
        }
    };

    // decode bytes to reserves + ts via alloy's abi decode
    let return_vals = getReservesCall::abi_decode_returns(value.data(), true)?;

    // Print emulated getReserves() call output
    println!("Reserve0: {:#?}", return_vals.reserve0);
    println!("Reserve1: {:#?}", return_vals.reserve1);
    println!("Timestamp: {:#?}", return_vals.blockTimestampLast);

    Ok(())
}
