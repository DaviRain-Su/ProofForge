# ProofForge.Evm

## Purpose

把 frontend `Core.IR.Program` 降成独立 EVM target IR，再编成 Yul / ABI / bytecode。
平行于 `Svm/`，不改 frontend `Core.IR.Program`。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Evm.Runtime` | 环境 opcode、`Addr20` / `UInt256`、LOG、hashed Map、封闭 ERC-20 | SVM sysvar / CPI |
| `Crypto.Keccak` | Ethereum Keccak-256、ABI selector（公共库） | 链上 opcode |
| `Evm.IR` | EVM-only `Op`、typed storage slot/Vector stride、constructor、selector、digest | Loader V3、账户 disc、SVM op |
| `Evm.Emit` | Core CFG → Yul + `abi.json`；环境、value、Addr20、位运算、for、下标、ABI、hashed Map、封闭 ERC-20、通用 LOG、pair-key allowance、event ABI、本合约 transfer/transferFrom | 任意 CALL / Token-2022 |
| `Evm.Assemble` | locked `solc 0.8.34` 子进程 | FFI、PATH 随便一个 solc |
| `Evm.Commands` | `#pf_evm_build` | 新 DSL |

输入是已通过 Profile 的 frontend `Core.IR.Program`。`Evm.IR.extractRegistration` 向
`Core.Target` 注册 extension 投影、arity / well-formed / CFG 合同；`Evm.IR.fromExtracted`
经通用投影后物化 storage slot 并把 source Ops 降成 EVM-only `Op`。`Extract.IR` 不再拥有
EVM conversion；SVM 叶子（`clockSlot` / `signerKey0` /
`systemTransfer`）在这个边界 fail closed，Yul emitter 不再承担跨 target 过滤。承认独立 EVM
叶子：环境 opcode（超 UInt64 revert）、8 字节 `evmCaller`/`evmSelf`、Addr20 三叶。
`evmDeposit` 让该 entry payable；程序若有任一 payable 入口，去掉全局 `callvalue()` 守卫，
非 payable 入口本地守卫。`evmSendEth` 是封闭 value CALL。`evmLogTipped` 是 LOG1。窄槽
`UInt8/16/32` 各占一个 storage word。`Option UInt64` 是 tag+payload 两槽。

每个 target-owned method 通过 `Method.toCFG` 后生成 Yul：入口预声明 CFG locals，`pf_pc`
dispatcher 的每个 `case` 对应一个 basic block，branch / checked success / overflow 只改下一
block id。`pf_last` 只显式承接原 ABI 的 checked/effect result；local 和 storage value 直接
按 CFG 中的显式引用读取，冲突 join fail closed。由于 Yul
没有 `goto`，该 dispatcher 是任意 reducible CFG 的统一边界，不再依赖 source 嵌套形状。
tuple return 由 CFG 的 `returnU64s` exit 一次编码为连续 ABI words。Constructor 也从
`lowerInit` 的唯一 `initialize` exit 取值；尚未建模的 constructor effect fail closed。

首选的 `init` / `initialize` → constructor；其它 `.init` 方法不会成为 runtime entry，避免部署后重置 storage。非 init 方法 → ABI entry；`Addr20` 参数/返回编成一个 `address`（IR 摊三叶）；`UInt256` 编成一个 `uint256`（IR 摊四叶，w0 最低）。`kind.get` 标 `view`；含 `evmDeposit` 的 mutate 标 `payable`。`evmLog name amt` 是 LOG1，topic = `keccak("name(uint64)")`。pair-key Map 是 `keccak256(owner||spender||base)`。

overflow 是 `revert(0, 0)`，不是 `0x1001`。定理仍钉用户 `def`。

## API

- `IR.fromExtracted : Extract.IR.Program → Except String IR.Program`
- `IR.extractRegistration : Core.Target.Registration … Evm.Ops.ValKind Evm.Ops.OpExt`
- `Emit.emitYul` / `Emit.emitAbi`
- `Assemble.assembleProgram`
- `#pf_evm_build Namespace`
- `#pf_evm_dump Namespace`（打抽出 ops / digest，不汇编）

## Tests

`Tests/EvmSpec.lean`、`Tests/EvmBuildSpec.lean`。solc 门在 `pfEvmAssemble`。

Anvil（工程门，不是 refinement）：

- `runtime-tests/evm/anvil_counter.sh`：constructor / increment / get / overflow
- `runtime-tests/evm/anvil_pair.sh`：constructor 只写 left；拒绝 runtime `initBoth`；`creditLeft` 保 right
- `runtime-tests/evm/anvil_flag.sh`：UInt8 mask + count 保持
- `runtime-tests/evm/anvil_maybe.sh`：none 清零、some 写双叶
- `runtime-tests/evm/anvil_ctx.sh`：`evmCaller` 对发送者低 8 字节；`height` 对 `block.number`
- `runtime-tests/evm/anvil_tipjar.sh`：chainid、timestamp、Addr20 三叶、`payout(address,uint256)`、精确 `deposit(uint256)`、错 value 保持、sendEth 改余额、Tipped log、空 calldata `receive()`
- `runtime-tests/evm/anvil_lang.sh`：位运算、mod-64 移位、`uint8` ABI、tuple return、运行时下标、有界 for、`oob` revert
- `runtime-tests/evm/anvil_vault.sh`：hashed Map UInt64/Addr20、`shareOf(address)` / `pull(address,address,uint256)`、封闭 `approve`/`transferFrom`/`allowance`、超额保持、USDT 无返回成功
- `runtime-tests/evm/anvil_ownable.sh`：`constructor(address)` / `ownerOf()(address)`、非 owner revert、Incremented log、`approve(address,address,uint64)` / allowance / spend
- `runtime-tests/evm/anvil_token.sh`：`mint(address,uint256)` / `transfer(address,uint256)` 扣余额、不足 `Insufficient(have,want)`、`approve(address,uint256)` / `transferFrom(address,address,uint256)` 扣额度、LOG3 Transfer/Approval
- `runtime-tests/evm/anvil_window.sh`：固定长 Vector 两槽；`setTail` 只写第二叶，第一叶保持
- `runtime-tests/evm/anvil_phase.sh`：零 payload variant 的 idle/live tag 往返与 view
- `runtime-tests/evm/anvil_wide.sh`：`uint256` ABI、跨 64-bit 边界 add/sub/mul、溢出 revert

入口：`runtime-tests/evm/anvil.sh`（Darwin / Linux）。工具查找：`FOUNDRY_BIN`、`~/.foundry/bin`、`PATH`。缺 `anvil`/`cast` 干净跳过。多个 `returnState` 按槽顺序 `sstore`，最后一次才 `return`。
