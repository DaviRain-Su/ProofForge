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

输入是已通过 Profile 的 `IR.Program`。拒绝 SVM 叶子、窄槽、Option 双叶。

`init` / `initialize` → constructor。其它方法 → `uint64` ABI entry；`kind.get` 标 `view`。

overflow 是 `revert(0, 0)`，不是 `0x1001`。定理仍钉用户 `def`。

## API

- `IR.fromProgram : SolanaLean.IR.Program → Except String IR.Program`
- `Emit.emitYul` / `Emit.emitAbi`
- `Assemble.assembleProgram`
- `#evm_build Namespace`

## Tests

`Tests/EvmSpec.lean`、`Tests/EvmBuildSpec.lean`。solc 门在 `evmLeanAssemble`。
