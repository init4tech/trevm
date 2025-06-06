//! This example demonstrates how to query storage slots of a contract, using
//! [`AlloyDb`].

use alloy::{
    eips::BlockId,
    primitives::{address, Address, TxKind, U256},
    providers::ProviderBuilder,
    sol,
    sol_types::SolCall,
};
use revm::{context::TxEnv, database::WrapDatabaseAsync};
use trevm::{db::alloy::AlloyDb, revm::database::CacheDB, NoopBlock, NoopCfg, TrevmBuilder, Tx};

sol! {
    #[allow(missing_docs)]
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
}

struct GetReservesFiller;

impl Tx for GetReservesFiller {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        tx_env.caller = Address::with_last_byte(0);
        // ETH/USDT pair on Uniswap V2
        tx_env.kind = TxKind::Call(POOL_ADDRESS);
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

    let client = ProviderBuilder::new().connect_http(rpc_url.parse()?);

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

    // initialize new AlloyDB
    let alloydb = WrapDatabaseAsync::new(AlloyDb::new(client, BlockId::default())).unwrap();

    // initialise empty in-memory-db
    let cache_db = CacheDB::new(alloydb);

    // initialise an empty (default) EVM
    let evm = TrevmBuilder::new()
        .with_db(cache_db)
        .build_trevm()?
        .fill_cfg(&NoopCfg)
        .fill_block(&NoopBlock)
        .fill_tx(&GetReservesFiller)
        .run()
        .inspect_err(|e| panic!("Execution error {e:?}"))
        .unwrap();

    // Inspect the outcome of a transaction execution, and get the return value
    println!("Execution result: {:#?}", evm.result());
    let output = evm.output().expect("Execution halted");

    // decode bytes to reserves + ts via alloy's abi decode
    let return_vals = getReservesCall::abi_decode_returns_validate(output)?;

    // Print emulated getReserves() call output
    println!("Reserve0: {:#?}", return_vals.reserve0);
    println!("Reserve1: {:#?}", return_vals.reserve1);
    println!("Timestamp: {:#?}", return_vals.blockTimestampLast);

    Ok(())
}
