# Runtime / SDK 双目标路线图

> 更新：2026-08-27。本文是 SVM 与 EVM 后续 Runtime / SDK 工作的权威排期；
> [backlog.md](backlog.md) 记录已经落地的证据和当前 Phoenix 切片。

## 1. 结论和边界

ProofForge 不是“在 sBPF / Yul 汇编上持续堆 helper”，而是用普通 Lean 4 组织三层能力：

```diagram
┌───────────────────────────────────────────────────────────┐
│ Shared language                                            │
│ 普通 Lean · Profile · Extract · Core CFG · checked control │
└────────────────────────────┬──────────────────────────────┘
                             │
              ┌──────────────┴──────────────┐
              ▼                             ▼
┌───────────────────────────┐  ┌────────────────────────────┐
│ SVM Runtime + Component   │  │ EVM Runtime + Component    │
│ account ABI/CPI/sysvar    │  │ ABI/storage/CALL/LOG/revert│
└─────────────┬─────────────┘  └──────────────┬─────────────┘
              ▼                               ▼
┌───────────────────────────┐  ┌────────────────────────────┐
│ SVM SDK                   │  │ EVM SDK                    │
│ Account/PDA/Token +       │  │ typed storage/context +    │
│ fixed-capacity containers │  │ reusable contract patterns │
└─────────────┬─────────────┘  └──────────────┬─────────────┘
              ▼                               ▼
┌───────────────────────────┐  ┌────────────────────────────┐
│ Examples.Phoenix / apps   │  │ Examples.Token / apps      │
└───────────────────────────┘  └────────────────────────────┘
```

只共享**语义和控制合同**，不共享 target 的物理状态模型：

- SVM 持久状态是 account bytes 上的 fixed stride / fixed capacity / index。`0` sentinel、
  zero-based 或 one-based 必须写进 descriptor；native pointer 永远不能进入 account。
- SVM transient allocation 是单次 invocation 内的 bounded downward bump heap。默认 32 KiB，
  可请求到 256 KiB，OOM 显式失败，`dealloc` 不回收。它不能实现持久 `Map` / `Vec`。
- EVM 持久状态是静态 slot、packed scalar、fixed array 和 hashed map namespace。
  `Storage.Layout` 只在抽取期分配 handle，不进入链上 storage。
- Phoenix layout、订单比较、撮合、手续费和 wire policy 只在 `Examples`。SDK 可以拥有
  RBMap/FIFO/allocator/codec 等通用物件，但不能拥有 Phoenix 名字、offset 或订单策略。

新能力首先判断它属于 SDK 组合、target component，还是一种确实无法表达的新底层 effect。
只有最后一种才允许扩 Ops / IR / target emitter。不能为 queue、map、allocator 或某个协议
instruction 增加 recipe opcode。

## 2. “完成”的可验收上限

本路线的“完成”不是声称支持任意 Rust crate、任意 Solidity、无界内存或所有未来协议；
它是下面这个 fail-closed v1 ceiling：

| 面 | v1 完成时可表达 | 明确 fail closed |
|---|---|---|
| Shared | 定宽整数/bytes、bounded tuple/record/enum codec plan、有界循环、checked control、显式 effect ordering | 一般递归、`IO`、FFI、无界 `Array` |
| SVM | 固定账户和 bounded remaining accounts、PDA/Signer/sysvar/CPI、classic Token 与已建模的 Token-2022 extension、return data/event | 持久 native pointer、无界 heap 容器、未建模 TLV/CPI |
| SVM storage SDK | POD field、fixed Vec/Queue、ordered Map/RBMap、one-based allocator、bounded cursor、transient scratch | 账户内 `HashMap`、跨 invocation heap、运行时任意 geometry |
| EVM | address/uint256/fixed bytes、static/fixed storage、typed hashed maps、bounded ABI、payable/event/revert、显式封闭 external call | `delegatecall`/proxy、运行时任意 callee、合约创建、无界动态 object graph |
| EVM contract SDK | access control、pause/reentrancy policy、safe value/token interaction、ERC fungible/NFT 基础形状 | 未单独建模的标准扩展、把 external call 假装成纯函数 |

超过 ceiling 的功能不是静默降级，而是在 Profile / Extract / component validation 中给出稳定
错误。以后可以逐项提高 ceiling，但不能以“覆盖所有范式”为名取消资源边界。

## 3. 当前基线

| 层 | 已有 | 主要缺口 |
|---|---|---|
| Shared | target registration、typed extension、Core CFG、bounded scalar frame、checked arithmetic/control、bounded codec schema/resource budget、allocation-free fixed bytes/u128/u256 source values、aggregate source-schema derivation；SVM/EVM scalar target binding | SVM/EVM aggregate target binding 与 cross-target aggregate fixture |
| SVM Runtime | Loader-v3 ABI、编译期账户下标、PDA/seeds、sysvar、通用 CPI words、System/Token wrappers、typed scalar Borsh entry/return | bounded remaining-account view；运行时安全账户索引；aggregate Borsh；更完整 instruction buffer；Token-2022 TLV 语义 |
| SVM Component | `AccountStorage`、RBMap/allocator/cursor、recorder、FIFO cancellation | 容器 facade 尚未统一；部分能力仍以具体 component 暴露；heap 目前只是准确模型而非 source lowering |
| EVM Runtime | Address/UInt128/UInt256/FixedBytes、typed scalar ABI、环境、hashed maps、LOG/revert、ETH、ERC-20/WETH/Uniswap/Permit closed calls | aggregate bounded ABI/storage 组合；call return/error 合同；缺少标准化资源/重入边界 |
| EVM SDK | `Storage.Layout` typed maps、Context/Immutable/Event/Revert/closed-call facade | scalar/struct/fixed-array layout facade；access-control/pausable/reentrancy 与 token/NFT reusable components |
| 应用 | Phoenix fixed N=4 与 Phoenix-v1 account profile；Token/Capped 等 EVM examples | Phoenix-v1 仍只覆盖部分 instruction/matching policy；跨 target conformance examples 不完整 |

## 4. 交付顺序

排期按依赖和稳定切片，而不是按文件数量。每一行是一个可独立 commit 的验收单元；
SVM 和 EVM target 工作交替推进，避免一个 target 长期挤掉另一个。

| 阶段 | 顺序 | 交付 | 验收门 |
|---|---:|---|---|
| R0 Ownership freeze（已完成） | 1 | runtime/component/SDK/app capability matrix；增加边界测试，阻止 `Examples` 直连 target emitter 或协议 policy 反向进入 target | capability matrix、CI anti-leak/import guard、全双目标回归；见 [R0-001](tasks/r0-001.md) |
| R1 Shared protocol values | 2 | fixed bytes、u128/u256 logical schema；bounded record/tuple/enum codec plan；SVM Borsh 与 EVM ABI 各自 lowering | 正反抽取测试；同一 logical fixture 两个 target 各自编码；未知/超长 fail closed |
| R2 SVM Runtime completion | 3 | bounded remaining accounts、safe dynamic account view、generic bounded instruction data/CPI/PDA/sysvar；Token-2022 TLV slices | Lean + Mollusk；权限/OOB/malformed/atomic failure；不得出现 persistent pointer |
| R3 SVM SDK completion | 4 | `Svm.Sdk` facade；Account/Signer/PDA/System/Token；fixed Vec/Queue/Map/RBMap/allocator；bounded transient scratch API | 至少两个非 Phoenix example 复用每类容器；Phoenix 只消费 SDK/Examples layout；Mollusk + Surfpool |
| R4 EVM Runtime completion | 5 | bounded ABI、scalar/struct/fixed-array/map storage、wide arithmetic/compare、environment/event/revert、closed call result contract | Lean + solc + Anvil；malformed calldata、overflow、revert 和 storage atomicity |
| R5 EVM SDK completion | 6 | typed storage declarations；Ownable/roles/Pausable/Reentrancy policy；safe ETH/ERC-20；ERC-20、ERC-721 与 bounded ERC-1155 core shapes | 至少两个独立 contracts 复用组件；ABI/event/error 对照；Anvil |
| R6 Cross-target hardening | 7 | shared semantic fixtures、resource bounds、artifact reproducibility、release/capability manifest、CI gates | 全 Lean、全 SVM/Mollusk、Surfpool Loader-v3、全 EVM/Anvil、clean reproducible build |

Phoenix `matchLimit=2` remainder posting 已作为 R0 前最后一个在途协议切片收口：它验证了
现有 scalar frame、RBMap、allocator、recorder 和 optional-return 能直接组合，未给 Phoenix
新增 Ops / IR / emitter case。R0 已冻结 capability ownership 并加入 CI anti-leak 门；当前
进入 R1 shared protocol values，不再开 Phoenix-only 底层工作。R1-001 已落地 bounded
`Core.Codec` descriptor 和 typed method metadata，并把 EVM selector/guard/ABI 从 width
sentinel 迁到 `Evm.Codec`；R1-002 source slice 已落地 shared allocation-free
`FixedBytes n` / u128/u256 values 与 fixed-limb extraction。R1-003 已分别完成 SVM typed
scalar exact-cursor Borsh 和 EVM u128/bytesN canonical ABI binding；R1-004 已完成 bounded
aggregate source-schema derivation 与 fail-closed target gate；R1-005 已完成 SVM static
record/product/fixed-vector Borsh binding。下一切片实现 EVM aggregate ABI，不统一两个
target 的物理 layout。

## 5. 阶段拆分

### R0 — ownership 和 anti-leak 门（已完成）

1. 已生成 source API → component → target effect 的
   [capability matrix](capability-matrix.md)。
2. CI checker 钉死主 target Runtime / Emit 只有 generic target/component bridge，拒绝协议名和
   application 反向依赖；canonical guards 继续固定既有 generic lowering。
3. `Examples` 可以声明 concrete layout 和 policy，但不能直接依赖 `*/Emit`。
4. `Projects/Phoenix` ownership 已删除；`ProofForge/Svm` 只保留通用组件。

交付证据见 [R0-001](tasks/r0-001.md)。R0 不新增语言能力；它固定后续 R1–R6 必须遵守的
ownership 和物理状态边界。

### R1 — shared value / protocol schema

R1-001 已完成 typed scalar/shape descriptor、资源预算、Core/SVM/EVM IR metadata transport，
以及 EVM scalar ABI adapter；详见 [R1-001](tasks/r1-001.md)。它保留 legacy width 只用于
Golden/Legacy compatibility，不把兼容 sentinel 当成新语言 API。

R1-002 source slice 已完成 allocation-free `UInt128`、shared `UInt256` 和 literal
`FixedBytes n`（`1 ≤ n ≤ 32`）以及 Extract fixed-limb metadata；详见
[R1-002](tasks/r1-002.md)。

R1-003 已完成 scalar target binding：SVM 使用 exact little-endian Borsh leaf/cursor plan，
EVM 使用 canonical numeric uint 与 source-order left-aligned bytesN ABI；详见
[R1-003](tasks/r1-003.md)。

R1-004 已从普通 Lean 类型推导 bounded tuple/record/enum/option/fixed-array schema，贯穿
Core/SVM/EVM IR，并在两个 target 的 aggregate adapter 完成前 fail closed；详见
[R1-004](tasks/r1-004.md)。

R1-005 已完成 SVM static aggregate binding：Core 只给 source-order typed path，SVM 独立
选择 Borsh widths、fixed locals 与 canonical Bool guard；record/product/literal-Vector 可用于
raw entry，generated aggregate ABI 与 tagged/dynamic policy 仍 fail closed；详见
[R1-005](tasks/r1-005.md)。

1. 已增加逻辑 `FixedBytes n`、`UInt128` 和 shared `UInt256` 的 source/profile 规则；fixed
   source limbs 不包含 target wire/account/storage geometry。
2. 定义 bounded codec schema：scalar、fixed bytes、tuple/record、enum、`Option`、固定/上限数组。
3. SVM adapter 实现 Borsh little-endian 与 exact cursor consumption；EVM adapter 实现
   32-byte ABI word、tuple head 和静态 bounded tail。
4. codec 只描述 wire，不拥有 account/storage geometry，也不执行业务 validation。

### R2 — SVM Runtime

按以下三刀完成，不能重新拆成 syscall 叶子清单：

- **SRT-1 Account view**：从 Loader account prefix 建 bounded account slice，静态账户与
  remaining accounts 使用同一 OOB/duplicate/writable/signer/owner gate；动态 index 只能来自
  已证明上界的 scalar。
- **SRT-2 Instruction/effects**：bounded instruction buffer、return data、PDA 多 seed、CPI meta
  与 signer seeds；sysvar access 统一成 target-owned query/call，scratch 区域合同显式化。
- **SRT-3 Token-2022**：TLV iterator 是 bounded byte cursor；按 extension 分片开放 transfer fee、
  transfer hook/account requirements 等语义。未知 extension 继续 fail closed，不能套 classic
  82/165-byte 路径。

### R3 — SVM SDK

SDK 按生命周期分两类，名字上也不能混：

- `AccountStorage`：持久 POD/Field、fixed Vec/Queue、ordered Map/RBMap、free-list allocator；
  descriptor 是编译期/抽取期 geometry，值是 account offset/index，不是 pointer。
- `Scratch`：invocation-local fixed/bounded Vec、byte writer、codec buffer；由 SVM bump allocator
  支撑，显式 capacity/OOM，离开 instruction 即失效。

`Account`、`Signer`、`Pda`、`System`、`Token`、`Token2022` facade 应直接组合已有
Runtime/Component，不增加“方便用”的 recipe opcode。Phoenix 用于证明复杂 orderbook 范式，
另外增加小型 Queue/Map examples，证明组件不是 Phoenix 专用品。

### R4 — EVM Runtime

1. ABI：`uint8..256`、address、fixed bytes、tuple/record、fixed array 和有上限的 calldata bytes；
   selector、calldata 长度、offset、padding 全部 fail closed。
2. Storage：scalar/struct/fixed array 静态 cursor 与 typed hashed map；布局在抽取期确定，禁止
   运行时 slot allocator。
3. Effects：完整环境 read、LOG0..4 的 typed plan、custom errors、receive/payable、closed
   CALL/STATICCALL 的 success/return-data contract。
4. arithmetic：UInt256 compare/bitwise/div/mod 和明确 overflow policy；不把 UInt64 默认规则
   偷套到 EVM word。

### R5 — EVM SDK

可复用组件拥有**合同策略和显式 handles**，不隐藏状态写入：

- access：Ownable、two-step ownership、bounded roles、Pausable、Reentrancy guard；
- assets：safe ETH、safe ERC-20/permit、fungible token ledger、ERC-721 owner/approval、
  bounded ERC-1155 balance/operator core；
- integration：WETH/router 等继续使用 typed closed calls，不开放任意 callee + 任意 calldata。

每个组件必须由两个不同 example 消费，且业务合约只 import `Evm.Sdk`，不能直接写 map base、
event topic 或 error selector 魔数。

### R6 — 双目标验收

- shared semantic fixtures：Counter、Escrow/Vault、Fungible ledger；共享行为规范，使用
  target-owned storage/ABI binding，不强求同一份物理 layout source。
- resource manifest：每个 program/contract 的 CFG blocks、locals、stack/scratch、account/storage
  geometry、assembly/ELF/bytecode size。
- reproducibility：pinned Lean、sbpf、solc、Surfpool、Mollusk、Anvil；同 checkout digest 与产物
  对应。
- CI：每个切片都跑全 Lean、全 target build 和相应 runtime suite。SVM 本地部署只用
  Surfpool 1.5.0 Loader-v3 transaction path，不使用 Test Validator。

## 6. 每个切片的 Definition of Done

1. source API 的 owner 和 lowering path 清楚；没有 one-use wrapper 或协议特判。
2. 成功、边界、malformed/OOB/权限、资源耗尽、原子失败都有测试。
3. 不支持的输入在 Profile/Extract/component validation fail closed，不到 emitter 猜语义。
4. SVM 跑 Lean + focused/full Mollusk；部署资格切片再跑 Surfpool。EVM 跑 Lean + solc + Anvil。
5. 两个 target 的 registry/build 回归都跑，防止共享层变更只验证一边。
6. 更新 capability matrix、digest/size 和 backlog；一个稳定切片一个 commit，不按小文件频繁推送。
