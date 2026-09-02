# ProofForge.Svm

## Purpose

把 frontend `IR.Program` 降成独立 SVM target IR，再编成 Solana sBPF / IDL / `.so`。
平行于 `Evm/`，不和公共抽出层混在一起。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Svm.Runtime` | sysvar / AccountInfo / CPI / PDA 宿主 stub | EVM opcode |
| `Svm.ABI` | account limits、discriminator、Loader V3/account byte layout、CPI account count | EVM storage |
| `Svm.Heap` | 32–256 KiB transient downward bump allocator 模型 | account data allocator、持久 pointer、无限 heap |
| `Svm.AccountStorage` | 固定 Region/Field/index、bounded account-resident map/queue/tree routine | transient heap object、runtime geometry |
| `Svm.AccountView` | compile-time `base`/`capacity` remaining-account window、runtime-safe index、read-only header/data 访问 | 写路径、persistent pointer、runtime geometry |
| `Svm.Sdk.Pubkey/Program/Token` | compiler-erased 32-byte key、canonical program id、exact SPL base-state view | 链上 base58、account copy、Token-2022 extension 猜测 |
| `Svm.BatchRecorder` | bounded begin/append/finish、SDK heap payload、dynamic signed self-CPI sink | persistent event container、source-visible pointer |
| `Svm.TransientVec` | source-visible fixed-capacity invocation-local `Vector64`、explicit full/OOB/state/OOM | persistent pointer、隐式增长、通用 heap collection |
| `Svm.Component` | 稳定 Query/Call bridge、effects/value traversal、component-owned emitter/scratch boundary | 业务协议语义、任意动态分配 |
| `Svm.IR` | SVM-only `Op`、account-data byte offset、Vector byte stride | EVM storage slot / EVM effect |
| `Svm.Solanalib` | bounded typed ALU/static-store semantics bridge | Loader、syscall、ELF、完整 emitter refinement |
| `Svm.Emit` | Loader V3 单账户 `.s`；checked 算术、CPI、sysvar | Yul、EVM opcode |
| `Svm.Idl` | Solana IDL spec 0.1.0 JSON | ABI JSON、链上字节 |
| `Svm.Assemble` | locked `sbpf 0.2.2` 子进程 | FFI、PATH 随便一个 sbpf |
| `Svm.Commands` | `#pf_check` / `#pf_extract` / `#pf_build` / `#pf_dump` | `#pf_evm_build` |

公开输入仍是已通过 Profile 的组合抽取 IR；`Svm.IR.extractRegistration` 向
`Core.Target` 注册 SVM extension 投影、arity / well-formed / CFG 合同。
`Svm.IR.fromExtracted` 经该通用边界投影 SVM Ops、物化 byte layout 并拒绝全部 EVM op，
`Extract.IR` 不再拥有 SVM conversion，`Svm.Emit` 只消费 SVM target `Program` / `Op`。位运算、命名
错误、有界 for / Vector 下标、wrapping add view 已开。disc / layout 域仍是
`proof-forge-solana-v1:` / `proof-forge-solana-layout-v1:`，不改现有 `.so` 字节。

上层 bounded feature 经统一 component lowering：

```text
source semantic helper
  → Svm.Component.Query / Call
  → component-owned validation, effects and emitter
  → sBPF
```

因此 generic `Svm.Ops.ValKind/OpExt`、`Svm.IR.Op`、CFG payload traversal 和主 `Svm.Emit`
各自只保留一个 `.component` case。新增 queue、audit recorder、allocator 或 codec 仍需要在
`Svm.Component` 内注册自己的 bounded vocabulary 和 backend，但不再改动上述通用层。
`AccountView` 是 remaining-account 的 component backend：compile-time `View{base, capacity}`
窗口加一个 runtime index，发射器先查 `index < capacity` 再查 `base + index < NUM_ACCOUNTS`，
然后沿真实账户头 walk（逐个验证 `0xff`/`NON_DUP_MARKER` tag）读取 header 字段或
`data_len`-checked 数据字；任何越界在读取任何字节前以 `Custom(1)` 原子失败。使用 view 的程序
切换到按 runtime `NUM_ACCOUNTS` 遍历、由 `maxTxAccountLocks` 硬上界约束的 walk 合同，并把
instruction data / program id 定位到实际最后一个账户之后；不使用 view 的程序保持原字节。
`Svm.Sdk.Account` 提供 fixed Account/Signer 和 bounded remaining-account `pf_inline` 句柄，
抽取期整体擦除。bounded view 是只读的。`Svm.Sdk.Pubkey/Program` 以四个 little-endian word
复用同一 key/owner leaves，`Token.AccountState/MintState` 再组合 exact 165/82-byte layout，
不创建 byte Array、heap parser 或协议专用 emitter。

`AccountStorage` 是第一个 component backend：它组合 compile-time `Region/Field`、显式
zero/one-based index、checked load/store 与有界 tree walk，而不是把每种容器做成新的底层
opcode。`BatchRecorder` 是第二个 backend：固定 header/record recipe 经 begin/append/finish
写入 invocation-local payload，达到 record/byte bound 就在 append 前 flush，finish 即使空 batch
也发 signed self-CPI。CPI detection、raw self-entry 和 scratch 需求都由 component capability
提供，generic IR/Emit 不枚举 recorder constructor。

`Svm.Heap` 单独建模官方 `BumpAllocator`：heap 映射在 `0x300000000`，默认 32 KiB，
compute-budget 上限 256 KiB；首 8 字节保存 bump，allocation 向下并向下对齐，OOM 返回
空，deallocation 不回收。这里的 transient heap 只活一个 invocation；账户内 Sokoban/Phoenix
allocator 仍是固定容量、index/offset based 的持久字节布局，绝不能保存 heap pointer。
账户内 allocator 与有界容器的关系见 [allocator-bounds.md](allocator-bounds.md)。
SDK global allocator 本身仍固定使用 32 KiB；`BatchRecorder` 因此不假设 Agave 可选的大 frame。
`Svm.Heap.Emit` 是这份协议的唯一 assembly interpreter，BatchRecorder 与
`Svm.TransientVec` 共用它。source-facing `Sdk.Transient.Vector64` 只携带编译期 capacity；
当前一个 invocation 默认两个 active slot（更多 handle 需 resource manifest 显式加界），payload 固定分配且 `finish` 不回收，full/OOB、
inactive/capacity mismatch、OOM 分别 fail with `0x1202`、`0x1203`、`0x1201`。native address
不进入 source value、IR value 或 account bytes。

## API

- `IR.fromExtracted : Extract.IR.Program → Except String Svm.IR.Program`
- `IR.extractRegistration : Core.Target.Registration … Svm.Ops.ValKind Svm.Ops.OpExt`
- `Emit.emitAsm : Svm.IR.Program → Except String String`
- `Idl.emitProgramIdl` / `Idl.discBytes` / `Idl.layoutDiscBytesProgram`
- `Assemble.assembleIRProgram`
- `fromProgram` / `emitCounterAsm` / `emitIdl` / `assembleProgram` 只保留旧 IR 兼容
- `#pf_build Namespace`
- `lake exe pfAssemble -- build/sbpf`
- `pf build --target svm`

细节见 [emit.md](emit.md)、[assemble.md](assemble.md)、[idl.md](idl.md)。

## Tests

`Tests/EmitSpec.lean`、`Tests/IdlSpec.lean`、`Tests/BuildSpec.lean`、
`Tests/SvmHeapSpec.lean`、`Tests/SvmTransientVectorSpec.lean`、`Tests/AccountViewSpec.lean`、
`Tests/SemanticsSpec.lean`（E2：Counter+Window emit→parse→step；见 [semantics-bridge.md](semantics-bridge.md)）。
汇编门在 `pfAssemble`。Mollusk 在 `runtime-tests/solana`。
