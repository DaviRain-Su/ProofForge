# ProofForge.Svm

## Purpose

把 frontend `IR.Program` 降成独立 SVM target IR，再编成 Solana sBPF / IDL / `.so`。
平行于 `Evm/`，不和公共抽出层混在一起。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Svm.Runtime` | sysvar / AccountInfo / CPI / PDA 宿主 stub | EVM opcode |
| `Svm.IR` | SVM-only `Op`、account-data byte offset、Vector byte stride | EVM storage slot / EVM effect |
| `Svm.Emit` | Loader V3 单账户 `.s`；checked 算术、CPI、sysvar | Yul、EVM opcode |
| `Svm.Idl` | Solana IDL spec 0.1.0 JSON | ABI JSON、链上字节 |
| `Svm.Assemble` | locked `sbpf 0.2.2` 子进程 | FFI、PATH 随便一个 sbpf |
| `Svm.Commands` | `#pf_check` / `#pf_extract` / `#pf_build` / `#pf_dump` | `#pf_evm_build` |

公开输入仍是已通过 Profile 的 frontend `ProofForge.IR.Program`；`Svm.IR.fromProgram` 先物化
byte layout 并拒绝全部 EVM op，`Svm.Emit` 只消费 SVM target `Program` / `Op`。位运算、命名
错误、有界 for / Vector 下标、wrapping add view 已开。disc / layout 域仍是
`proof-forge-solana-v1:` / `proof-forge-solana-layout-v1:`，不改现有 `.so` 字节。

## API

- `IR.fromProgram : ProofForge.IR.Program → Except String Svm.IR.Program`
- `Emit.emitCounterAsm : ProofForge.IR.Program → Except String String`
- `Idl.emitIdl` / `Idl.discBytes` / `Idl.layoutDiscBytes`
- `Assemble.assembleProgram`
- `#pf_build Namespace`
- `lake exe pfAssemble -- build/sbpf`
- `pf build --target svm`

细节见 [emit.md](emit.md)、[assemble.md](assemble.md)、[idl.md](idl.md)。

## Tests

`Tests/EmitSpec.lean`、`Tests/IdlSpec.lean`、`Tests/BuildSpec.lean`。汇编门在 `pfAssemble`。Mollusk 在 `runtime-tests/solana`。
