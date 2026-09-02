# ProofForge.Evm

## Purpose

把 frontend `Core.IR.Program` 降成独立 EVM target IR，再编成 Yul / ABI / bytecode。
平行于 `Svm/`，不改 frontend `Core.IR.Program`。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Evm.Sdk` | 合同侧 `Address` / `UInt256`、静态 storage layout、typed map、checked fungible ledger、explicit reentrancy policy、bounded persistent vector/bitmap/ring/enumerable-set policy、context / immutable / event / revert / closed-call facade | SVM 账户几何、业务协议、运行时 layout 对象 |
| `Evm.Runtime` | 环境 opcode、`Addr20` / `UInt256`、LOG、hashed Map、封闭 ERC-20 | SVM sysvar / CPI |
| `Crypto.Keccak` | Ethereum Keccak-256、ABI selector（公共库） | 链上 opcode |
| `Evm.IR` | EVM-only `Op`、typed storage slot/Vector stride、constructor、selector、digest | Loader V3、账户 disc、SVM op |
| `Evm.Component` | 稳定 Query/Call 桥、effects/value 遍历、component-owned emitter | 业务协议语义、任意 CALL |
| `Evm.Emit` | Core CFG → Yul + `abi.json`；环境、value、Addr20、位运算、for、下标、ABI、hashed Map、封闭 ERC-20、通用 LOG、pair-key allowance、event ABI、本合约 transfer/transferFrom | 任意 CALL / Token-2022 |
| `Evm.Assemble` | locked `solc 0.8.34` 子进程 | FFI、PATH 随便一个 solc |
| `Evm.Commands` | `#pf_evm_build` | 新 DSL |

上层封闭能力经统一 component lowering：

```text
source semantic helper
  → Evm.Component.Query / Call
  → component-owned validation, effects and emitter
  → Yul
```

因此 generic `Evm.Ops.ValKind/OpExt`、`Evm.IR.Op`、CFG payload traversal 和主 `Evm.Emit`
各自只保留一个 `.component` case。hashed-map 读写、packed 256-bit 比较/算术、以及封闭 ERC-20 / WETH / Uniswap / permit
已经迁进 `Evm.HashedMap` / `Evm.WideWord` / `Evm.ClosedCall` / `Evm.NativeFx`。合同默认只打开
`Evm.Sdk`：`Storage.Layout` 用编译期 cursor 分配互不重叠的 map namespace；
`AddressMap256` / `AddressPairMap256` 提供 `get` / `put` / `containsAtLeast` /
`nextAdd` / `nextSub` / `revertInsufficient`；`Context`、`Immutable`、`Event`、`Revert`、
`ERC20`、`WETH`、`UniswapV2`、`Permit` 隔离 target runtime 名字。layout descriptor 只在
抽取期存在，不进 EVM storage，也没有魔数泄漏进合同源代码。SVM 不复用这套 layout：它的
持久容器仍由 account bytes / fixed stride / one-based index 描述。

`Sdk.Fungible.Balances` 把显式 `AddressMap256` handle 组合成 O(1) checked balance movement；
`Sdk.Fungible.Allowances` 把显式 `AddressPairMap256` handle 组合成 approve、checked
increase/decrease/spend 与 Insufficient contract。Token、Credits、Vault、Ownable 分别复用。
credit/increase 以 `next ≥ current` 拒绝 UInt256 wrap；transfer alias 不重复写 hashed key；
decrease/spend 先验证 current ≥ amount。权限、pause、supply/cap、permit 和 event policy 仍在
应用；这不是隐藏完整 ERC-20 的 recipe。

`Sdk.Reentrancy` 组合一个 explicit `Storage.Static.Handle UInt64`、OpenZeppelin-compatible
nonzero sentinels 和既有 ordered `storeNow` effect。应用显式书写 enter → closed CALL → leave，
hostile callback 可见 entered 状态，failed CALL 由交易回滚 lock；没有 raw slot、hidden State
write 或 Reentrancy-specific Ops/IR/Emit recipe。

`Sdk.StorageEnumerableSet` 把 fixed `Vector UInt64 capacity`、explicit live count 与
key→position+1 `U64Map` 组合为 O(1) insert/contains/indexed access/swap-remove policy。
position zero 保留给 absent，所以 key zero 仍可表示；descriptor 统一 capacity 与 map namespace，
decision 在任何 write 前拒绝 malformed count、伪造 position 与 backing mismatch。consumer
继续显式写 ordinary State vector/count 并执行 map put；SDK 不隐藏 storage effect，也不提供
需要 O(n) mapping clear 的 bulk clear。

SDK facade 直接 `@[pf_inline]` 到既有 source/runtime 叶，不增加 Ops、IR 或 emitter case；
canonical 拼写仍是 `vg` / `mseta256` / `ttxfer` / `permit` / `edep` /
`elog3.Transfer` / `err.ZeroAddress`。仅 facade adoption 保持旧产物；checked credit/alias-safe
transfer 是有意的行为修复，由 Registry digest、solc 与 Anvil 回归锁定。
Extract
写/读路径展开 Source 后只认 `opOfRuntimeApp` / `queryOfRuntimeApp`，不再按 recipe 名枚举
walker。新增 LOG 配方仍在 `Evm.Component` 内注册，不再改动上述通用层。

输入是已通过 Profile 的 frontend `Core.IR.Program`。`Evm.IR.extractRegistration` 向
`Core.Target` 注册 extension 投影、arity / well-formed / CFG 合同；`Evm.IR.fromExtracted`
经通用投影后物化 storage slot 并把 source Ops 降成 EVM-only `Op`。`Extract.IR` 不再拥有
EVM conversion；SVM 叶子（`clockSlot` / `signerKey0` /
`systemTransfer`）在这个边界 fail closed，Yul emitter 不再承担跨 target 过滤。承认独立 EVM
叶子：环境 opcode（超 UInt64 revert）、8 字节 `evmCaller`/`evmSelf`、Addr20 三叶。
`evmDeposit` 让该 entry payable；程序若有任一 payable 入口，去掉全局 `callvalue()` 守卫，
非 payable 入口本地守卫。`evmSendEth` 是封闭 value CALL。`evmLogTipped` 是 LOG1。窄槽
`UInt8/16/32` 各占一个 storage word。`Option UInt64` 是 tag+payload 两槽。

同一 successful transition 同时包含 component effect 与 ordinary State store 时，Extract 会先
snapshot 后续依赖的 mutable target query，再按 effect → State stores → return 排序。这样 map
write 或 CALL 不会让后续 vector/count write 重读已经改变的 storage；LOG 不会使 storage
query 失效，因此不触发额外 snapshot。多 limb/leaf State store 也不会由前一 leaf 污染共同
pre-state。query/effect 的可变性来自
`Component.Query.effects` / `Component.Call.effects`，不是协议或容器名特判。

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

`Tests/EvmSpec.lean`、`Tests/EvmSdkSpec.lean`、`Tests/EvmBuildSpec.lean`。solc 门在
`pfEvmAssemble`。

Anvil（工程门，不是 refinement）：

- `runtime-tests/evm/anvil_counter.sh`：constructor / increment / get / overflow
- `runtime-tests/evm/anvil_pair.sh`：constructor 只写 left；拒绝 runtime `initBoth`；`creditLeft` 保 right
- `runtime-tests/evm/anvil_flag.sh`：UInt8 mask + count 保持
- `runtime-tests/evm/anvil_maybe.sh`：none 清零、some 写双叶
- `runtime-tests/evm/anvil_ctx.sh`：`evmCaller` 对发送者低 8 字节；`height` 对 `block.number`
- `runtime-tests/evm/anvil_reentrancy.sh`：normal CALL、hostile nested callback rejection、failed-CALL rollback
- `runtime-tests/evm/anvil_tipjar.sh`：chainid、timestamp、Addr20 三叶、`payout(address,uint256)`、精确 `deposit(uint256)`、错 value 保持、sendEth 改余额、Tipped log、空 calldata `receive()`
- `runtime-tests/evm/anvil_lang.sh`：位运算、mod-64 移位、`uint8` ABI、tuple return、运行时下标、有界 for、`oob` revert
- `runtime-tests/evm/anvil_vault.sh`：hashed Map UInt64/Addr20、`shareOf(address)` / `pull(address,address,uint256)`、封闭 `approve`/`transferFrom`/`allowance`、超额保持、USDT 无返回成功
- `runtime-tests/evm/anvil_ownable.sh`：`constructor(address)` / `ownerOf()(address)`、非 owner revert、Incremented log、UInt256 approve / checked allowance spend / over-spend atomicity
- `runtime-tests/evm/anvil_token.sh`：checked additive mint、direct/delegated self-transfer、checked allowance increase/decrease/spend、wrap/不足原子保持、LOG3 Transfer/Approval
- `runtime-tests/evm/anvil_capped.sh`：第二个合约复用 owner + pause + 固定 cap；非 owner / paused / 超 cap 分别解码 Unauthorized / Paused / CapExceeded
- `runtime-tests/evm/anvil_allowlist.sh`：owner-gated set insert/zero-key/contains/index/swap-remove/full/malformed atomicity
- `runtime-tests/evm/anvil_id_registry.sh`：permissionless set reuse、typed full error、nonreverting malformed membership fallback
- `runtime-tests/evm/anvil_window.sh`：固定长 Vector 两槽；`setTail` 只写第二叶，第一叶保持
- `runtime-tests/evm/anvil_phase.sh`：零 payload variant 的 idle/live tag 往返与 view
- `runtime-tests/evm/anvil_wide.sh`：`uint256` ABI、跨 64-bit 边界 add/sub/mul、typed compare、bitwise/shift、溢出 revert
- `runtime-tests/evm/anvil_bounded.sh`：`echoBoundedWide` / `echoBoundedPairs` OK + malformed/over-capacity calldata
- `runtime-tests/evm/anvil_aggregate_storage.sh`：nested `Bundle`/`Details` admin writes、leaf views、`bundleSignal`、Unauthorized

入口：`runtime-tests/evm/anvil.sh`（Darwin / Linux）。工具查找：`FOUNDRY_BIN`、`~/.foundry/bin`、`PATH`。缺 `anvil`/`cast` 干净跳过。多个 `returnState` 按槽顺序 `sstore`，最后一次才 `return`。
