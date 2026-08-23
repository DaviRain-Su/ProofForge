# ProofForge.Evm

## Purpose

把 frontend `IR.Program` 降成独立 EVM target IR，再编成 Yul / ABI / bytecode。
平行于 `Svm/`，不改 frontend `IR.Program`。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Evm.Runtime` | 环境 opcode、Addr20、LOG、hashed Map、封闭 ERC-20 | SVM sysvar / CPI |
| `Crypto.Keccak` | Ethereum Keccak-256、ABI selector（公共库） | 链上 opcode |
| `Evm.IR` | EVM-only `Op`、typed storage slot/Vector stride、constructor、selector、digest | Loader V3、账户 disc、SVM op |
| `Evm.Emit` | Yul + `abi.json`；环境、value、Addr20、位运算、for、下标、ABI、hashed Map、封闭 ERC-20、通用 LOG、pair-key allowance、event ABI、本合约 transfer/transferFrom | 任意 CALL / Token-2022 |
| `Evm.Assemble` | locked `solc 0.8.34` 子进程 | FFI、PATH 随便一个 solc |
| `Evm.Commands` | `#pf_evm_build` | 新 DSL |

输入是已通过 Profile 的 frontend `IR.Program`。`Evm.IR.fromProgram` 物化 storage slot 并把
compatibility Ops 降成 EVM-only `Op`；SVM 叶子（`clockSlot` / `signerKey0` /
`systemTransfer`）在这个边界 fail closed，Yul emitter 不再承担跨 target 过滤。承认独立 EVM
叶子：环境 opcode（超 UInt64 revert）、8 字节 `evmCaller`/`evmSelf`、Addr20 三叶。
`evmDeposit` 让该 entry payable；程序若有任一 payable 入口，去掉全局 `callvalue()` 守卫，
非 payable 入口本地守卫。`evmSendEth` 是封闭 value CALL。`evmLogTipped` 是 LOG1。窄槽
`UInt8/16/32` 各占一个 storage word。`Option UInt64` 是 tag+payload 两槽。

`init` / `initialize` → constructor。其它方法 → `uint64` ABI entry；`kind.get` 标 `view`；含 `evmDeposit` 的 mutate 标 `payable`。`evmLog name amt` 是 LOG1，topic = `keccak("name(uint64)")`。pair-key Map 是 `keccak256(owner||spender||base)`。

overflow 是 `revert(0, 0)`，不是 `0x1001`。定理仍钉用户 `def`。

## API

- `IR.fromProgram : ProofForge.IR.Program → Except String IR.Program`
- `Emit.emitYul` / `Emit.emitAbi`
- `Assemble.assembleProgram`
- `#pf_evm_build Namespace`
- `#pf_evm_dump Namespace`（打抽出 ops / digest，不汇编）

## Tests

`Tests/EvmSpec.lean`、`Tests/EvmBuildSpec.lean`。solc 门在 `pfEvmAssemble`。

Anvil（工程门，不是 refinement）：

- `runtime-tests/evm/anvil_counter.sh`：constructor / increment / get / overflow
- `runtime-tests/evm/anvil_pair.sh`：constructor 只写 left；`initBoth` 写两槽；`creditLeft` 保 right
- `runtime-tests/evm/anvil_flag.sh`：UInt8 mask + count 保持
- `runtime-tests/evm/anvil_maybe.sh`：none 清零、some 写双叶
- `runtime-tests/evm/anvil_ctx.sh`：`evmCaller` 对发送者低 8 字节；`height` 对 `block.number`
- `runtime-tests/evm/anvil_tipjar.sh`：chainid、timestamp、Addr20 三叶、精确 deposit、错 value 保持、sendEth 改余额、Tipped log
- `runtime-tests/evm/anvil_lang.sh`：位运算、移位越界、`uint8` ABI、tuple return、运行时下标、有界 for、`oob` revert
- `runtime-tests/evm/anvil_vault.sh`：hashed Map UInt64/Addr20、ERC-20 transfer、超额保持、USDT 无返回成功
- `runtime-tests/evm/anvil_ownable.sh`：owner 三槽、非 owner revert、Incremented log、approve / allowance / spend、超额额度保持
- `runtime-tests/evm/anvil_token.sh`：mint / transfer 扣余额、不足 revert、approve / transferFrom 扣额度、Transfer/Approval log

入口：`runtime-tests/evm/anvil.sh`（Darwin / Linux）。工具查找：`FOUNDRY_BIN`、`~/.foundry/bin`、`PATH`。缺 `anvil`/`cast` 干净跳过。多个 `returnState` 按槽顺序 `sstore`，最后一次才 `return`。
