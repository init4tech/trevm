# Skill: trevm

Use when writing code that uses the trevm crate — especially EVM calls,
gas estimation, transaction execution, and block lifecycle management.

## Trevm EVM Lifecycle

Trevm wraps `revm` with a **typestate pattern**. The compiler enforces correct
usage order. State transitions are zero-cost (transmute between zero-sized
marker types).

```
TrevmBuilder::new()
    .with_db(db)            // required
    .with_inspector(insp)   // optional (default: NoOpInspector)
    .with_spec_id(spec)     // optional (default: PRAGUE)
    .build_trevm()          // -> EvmNeedsCfg
```

### State Machine

```
EvmNeedsCfg
    │ fill_cfg(&cfg)
    ▼
EvmNeedsBlock
    │ fill_block(&block)    [or drive_block / drive_chain / finish]
    ▼
EvmNeedsTx
    │ fill_tx(&tx)          [or run_tx / call_tx / estimate_tx_gas / close_block]
    ▼
EvmReady
    │ run()                 [or call / estimate_gas / clear_tx]
    ▼
┌─────────────┬──────────────┐
│EvmTransacted│  EvmErrored  │
│ accept()    │ discard_error│ ──► EvmNeedsTx
│ reject()    │ into_error() │
└─────────────┴──────────────┘
    │ accept() or reject()
    ▼
EvmNeedsTx ──close_block()──► EvmNeedsBlock ──finish()──► BundleState
```

### Filler Traits

`Cfg`, `Block`, and `Tx` are traits that fill revm's environment structs.
They must fill ALL fields (EVM does NOT clear between calls). Closures,
raw env types, and `Arc<dyn Trait>` all implement these traits.

```rust
// Closure-based fillers work:
evm.fill_cfg(&|cfg: &mut CfgEnv| { cfg.chain_id = 1; });

// Or implement the trait on your own types:
impl Tx for MyTransaction {
    fn fill_tx_env(&self, tx_env: &mut TxEnv) {
        let TxEnv { caller, gas_limit, kind, value, data, nonce, .. } = tx_env;
        *caller = self.from;
        // ... fill all fields
    }
}
```

## Common Patterns

### Simple Transaction Execution

```rust
use trevm::{TrevmBuilder, Cfg, Block, Tx};
use revm::database::in_memory_db::InMemoryDB;

let result = TrevmBuilder::new()
    .with_db(InMemoryDB::default())
    .build_trevm()
    .fill_cfg(&cfg)
    .fill_block(&block)
    .run_tx(&tx);

// Handle result
let evm = match result {
    Ok(t) => {
        let gas = t.gas_used();
        let output = t.output();
        t.accept_state()    // commit state changes
        // or t.reject()    // discard state changes
    }
    Err(e) => e.discard_error(),
};
```

### Simulated Call (feature = "call")

`call()` simulates a transaction **without** committing state changes.
It automatically disables EIP-3607, base fee checks, and nonce checks.

```rust
// From EvmReady (two-step):
let (execution_result, evm) = evm
    .fill_cfg(&cfg)
    .fill_block(&block)
    .fill_tx(&tx)
    .call()           // returns Result<(ExecutionResult, EvmNeedsTx), EvmErrored>
    .unwrap();

// From EvmNeedsTx (one-step shortcut):
let (execution_result, evm) = evm
    .fill_cfg(&cfg)
    .fill_block(&block)
    .call_tx(&tx)     // fill_tx + call in one step
    .unwrap();
```

### Gas Estimation (feature = "estimate_gas")

`estimate_gas()` uses binary search to find minimum gas. Returns an
`EstimationResult` (Success/Revert/Halt).

```rust
// From EvmReady:
let (estimation, evm) = evm
    .fill_cfg(&cfg)
    .fill_block(&block)
    .fill_tx(&tx)
    .estimate_gas()   // returns Result<(EstimationResult, EvmReady), EvmErrored>
    .unwrap();

// From EvmNeedsTx (shortcut):
let (estimation, evm) = evm
    .fill_cfg(&cfg)
    .fill_block(&block)
    .estimate_tx_gas(&tx)
    .unwrap();

// Check result
match estimation {
    EstimationResult::Success { gas_used, .. } => { /* use gas_used */ }
    EstimationResult::Revert { reason, .. } => { /* handle revert */ }
    EstimationResult::Halt { reason, .. } => { /* handle halt */ }
}
```

### Multi-Transaction Block Loop

```rust
let mut evm = TrevmBuilder::new()
    .with_db(state)
    .build_trevm()
    .fill_cfg(&cfg)
    .fill_block(&block);

for tx in transactions {
    evm = match evm.run_tx(&tx) {
        Ok(t) => t.accept_state(),
        Err(e) => e.discard_error(),
    };
}

let bundle = evm.close_block().finish();
```

### Decoding Solidity Return Values

```rust
use alloy::sol;
sol! { function balanceOf(address) returns (uint256); }

let (result, evm) = evm.call_tx(&tx).unwrap();
let balance = result.output()
    .map(|out| balanceOfCall::abi_decode_returns(out))
    .unwrap();
```

### EvmTransacted has a convenience method for this:

```rust
let t = evm.run_tx(&tx).unwrap();
let ret = t.output_sol::<balanceOfCall>(true).unwrap().unwrap();
```

## Key Types

| Type | Description |
|------|-------------|
| `Trevm<Db, Insp, State>` | Core wrapper, parameterized by DB, inspector, typestate |
| `EvmNeedsCfg<Db, Insp>` | Awaiting `fill_cfg` |
| `EvmNeedsBlock<Db, Insp>` | Awaiting `fill_block` or `drive_block` |
| `EvmNeedsTx<Db, Insp>` | Awaiting `fill_tx`, `run_tx`, `call_tx`, or `close_block` |
| `EvmReady<Db, Insp>` | Awaiting `run`, `call`, `estimate_gas`, or `clear_tx` |
| `EvmTransacted<Db, Insp>` | Has result; `accept` or `reject` |
| `EvmErrored<Db, Insp, E>` | Has error; `discard_error` or `into_error` |
| `EstimationResult` | Gas estimation outcome (Success/Revert/Halt) |
| `TrevmBuilder` | Builder with typestate (BuilderNeedsDb -> BuilderReady) |

## Type Aliases Macro

```rust
use trevm::trevm_aliases;
// Generates: EvmNeedsCfg, EvmNeedsBlock, EvmNeedsTx, EvmReady, etc.
// with concrete Db and Insp types
trevm_aliases!(MyDb);               // Insp defaults to NoOpInspector
trevm_aliases!(MyDb, MyInspector);   // explicit inspector
```

## Test Utilities (feature = "test-utils")

```rust
use trevm::test_utils::{test_trevm, test_trevm_with_funds, ALICE, BOB};

let mut evm = test_trevm();                       // InMemoryDB + NoOpInspector
evm.test_set_balance(ALICE.address(), U256::from(1_000_000));
evm.test_set_nonce(ALICE.address(), 1);
evm.test_set_bytecode(addr, bytecode);
evm.test_set_storage(addr, slot, value);

// Or pre-fund in one shot:
let evm = test_trevm_with_funds(&[
    (ALICE.address(), U256::from(1_000_000)),
]);
```

## Key Source Files

| File | Contents |
|------|----------|
| `src/lib.rs` | Crate root, docs, re-exports |
| `src/evm/builder.rs` | `TrevmBuilder` |
| `src/evm/need_cfg.rs` | `fill_cfg` |
| `src/evm/need_block.rs` | `fill_block`, `drive_block`, `drive_chain`, `finish` |
| `src/evm/need_tx.rs` | `fill_tx`, `run_tx`, `call_tx`, `estimate_tx_gas`, `close_block` |
| `src/evm/ready.rs` | `run`, `call`, `estimate_gas`, `clear_tx` |
| `src/evm/transacted.rs` | `accept`, `reject`, `output_sol`, result accessors |
| `src/evm/errored.rs` | `discard_error`, `into_error`, `map_err` |
| `src/evm/states.rs` | Typestate markers, sealed traits, `trevm_aliases!` |
| `src/fill/traits.rs` | `Cfg`, `Block`, `Tx` trait definitions |
| `src/fill/fillers.rs` | `CallFiller`, `GasEstimationFiller`, `NoopCfg`, `NoopBlock` |
| `src/est.rs` | `EstimationResult`, `SearchRange` |
| `src/helpers.rs` | `Ctx`, `Evm`, `Instructions` type aliases |
| `src/test_utils.rs` | `test_trevm`, `ALICE`, `BOB`, `TestInspector` |
