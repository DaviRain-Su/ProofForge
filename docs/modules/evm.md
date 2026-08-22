# SolanaLean.Evm

## Purpose

把同一套抽出 Ops 编成 EVM Yul / ABI / bytecode。平行于 sBPF 发射器，不改 `IR.Program`。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Evm.Keccak` | Ethereum Keccak-256、ABI selector | SHA-256、链上 opcode |
| `Evm.IR` | storage slot、constructor、selector、digest | Loader V3、账户 disc |
| `Evm.Emit` | Counter 级 Yul + `abi.json` | Map / CALL / payable |
| `Evm.Assemble` | locked `solc 0.8.34` 子进程 | FFI、PATH 随便一个 solc |
| `Evm.Commands` | `#evm_build` | 新 DSL |

输入是已通过 Profile 的 `IR.Program`。拒绝 SVM 叶子。窄槽 `UInt8/16/32` 各占一个 storage word，低字节 `and`。`Option UInt64` 是 tag+payload 两槽。

`init` / `initialize` → constructor。其它方法 → `uint64` ABI entry；`kind.get` 标 `view`。

overflow 是 `revert(0, 0)`，不是 `0x1001`。定理仍钉用户 `def`。

## API

- `IR.fromProgram : SolanaLean.IR.Program → Except String IR.Program`
- `Emit.emitYul` / `Emit.emitAbi`
- `Assemble.assembleProgram`
- `#evm_build Namespace`

## Tests

`Tests/EvmSpec.lean`、`Tests/EvmBuildSpec.lean`。solc 门在 `evmLeanAssemble`。

Anvil（工程门，不是 refinement）：

- `runtime-tests/evm/anvil_counter.sh`：constructor / increment / get / overflow
- `runtime-tests/evm/anvil_pair.sh`：constructor 只写 left；`initBoth` 写两槽；`creditLeft` 保 right
- `runtime-tests/evm/anvil_flag.sh`：UInt8 mask + count 保持
- `runtime-tests/evm/anvil_maybe.sh`：none 清零、some 写双叶

入口：`runtime-tests/evm/anvil.sh`（Darwin / Linux）。工具查找：`FOUNDRY_BIN`、`~/.foundry/bin`、`PATH`。缺 `anvil`/`cast` 干净跳过。多个 `returnState` 按槽顺序 `sstore`，最后一次才 `return`。
