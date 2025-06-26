# Trevm Examples

This directory contains comprehensive examples demonstrating various aspects of the Trevm library.

## Examples Overview

### 1. `basic_transact.rs`
Basic contract interaction example showing:
- Contract deployment to memory database
- Simple contract call execution
- Basic transaction handling

**Run with:**
```bash
cargo run --example basic_transact
```

### 2. `fork_ref_transact.rs`
Mainnet forking example demonstrating:
- Querying real Ethereum state using AlloyDb
- Calling live contracts (Uniswap V2 pair)
- Reading storage slots from mainnet

**Run with:**
```bash
cargo run --example fork_ref_transact --features alloy-db
```

### 3. `trevm_basic_example.rs`
Simple Trevm usage showing:
- Type-safe transaction building
- Error handling patterns
- State management

**Run with:**
```bash
cargo run --example trevm_basic_example
```

### 4. `trevm_inspector_example.rs`
Advanced example with inspector integration:
- Contract deployment with tracing
- EIP-3155 tracer integration
- Multi-transaction workflow

**Run with:**
```bash
cargo run --example trevm_inspector_example
```

### 5. `trevm_block_driver_example.rs`
Block processing example showing:
- Custom BlockDriver implementation
- Multi-transaction batching
- Receipt generation

**Run with:**
```bash
cargo run --example trevm_block_driver_example
```

### 6. `tx_tracer_cli.rs` 🎯
**CLI tool for tracing any Ethereum transaction:**
- Fetches transaction from mainnet
- Replays with detailed EIP-3155 tracing
- Shows state changes and execution details

**Run with:**
```bash
cargo run --example tx_tracer_cli --features alloy-db -- <tx_hash> [rpc_url]
```

**Example usage:**
```bash
# Trace a specific transaction
cargo run --example tx_tracer_cli --features alloy-db -- 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef

# Use custom RPC endpoint
cargo run --example tx_tracer_cli --features alloy-db -- 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef https://mainnet.infura.io/v3/YOUR_KEY
```

## Key Concepts Demonstrated

### Typestate Pattern
All examples show how Trevm's typestate pattern prevents common EVM usage errors:
- Can't execute without configuration
- Can't apply state without successful execution
- Compile-time enforcement of correct state transitions

### Error Handling
Examples demonstrate proper error handling:
- `accept_state()` for successful transactions
- `discard_error()` for failed transactions
- Type-safe error recovery

### Database Integration
Various database backends:
- `InMemoryDB` for testing
- `AlloyDb` for mainnet forking
- `CacheDB` for performance optimization

### Inspector Integration
Examples show how to integrate revm inspectors:
- `NoOpInspector` for basic usage
- `TracerEip3155` for detailed tracing
- Custom inspectors for specialized needs

## Building and Running

All examples can be built with:
```bash
cargo build --examples
```

For examples requiring network access (alloy-db feature):
```bash
cargo build --examples --features alloy-db
```

## Usage in Your Projects

These examples serve as templates for common Trevm usage patterns:

1. **Testing contracts**: Use `trevm_basic_example.rs` pattern
2. **Mainnet simulation**: Use `fork_ref_transact.rs` pattern  
3. **Transaction tracing**: Use `trevm_inspector_example.rs` pattern
4. **Block processing**: Use `trevm_block_driver_example.rs` pattern
5. **CLI tools**: Use `tx_tracer_cli.rs` pattern