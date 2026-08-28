# Runtime / SDK 双目标路线图

> 更新：2026-08-27。本文是 SVM 与 EVM 后续 Runtime / SDK 工作的权威排期；
> [backlog.md](backlog.md) 记录已经落地的证据和当前 Phoenix 切片。
> 多 agent 并行时的 write set、shared-lock 和交付合同见
> [并行开发执行图](parallel-workstreams.md)。

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
| Shared | target registration、typed extension、Core CFG、bounded scalar frame、checked arithmetic/control、bounded codec schema/resource budget、allocation-free fixed bytes/u128/u256 source values、compiler-erased `BoundedVec` input carrier、aggregate source-schema derivation、target-neutral static projection/rewrite traversal；SVM/EVM scalar、static aggregate、tagged 与 bounded input target binding；同一 logical schema 的 cross-target plan conformance | tagged/bounded return source contract 与更高 resource ceiling |
| SVM Runtime | Loader-v3 ABI、编译期账户下标、PDA/seeds、sysvar、通用 CPI words、System/Token wrappers、typed scalar/static aggregate Borsh entry/return、Option/payload-enum tagged input、fixed-capacity canonical Borsh Vec input | bounded remaining-account view；运行时安全账户索引；tagged/bounded return policy；更完整 instruction buffer；Token-2022 TLV 语义 |
| SVM Component / SDK | `AccountStorage`、RBMap/allocator/cursor、recorder、FIFO cancellation；`Svm.Sdk` 已统一 POD Field、fixed Vec/Queue、ordered Map/RBMap、one-based allocator 和 canonical initialization | Account/Signer/PDA/System/Token facade 尚未统一；部分能力仍以具体 component 暴露；heap 目前只是准确模型而非 source lowering |
| EVM Runtime | Address/UInt128/UInt256/FixedBytes、typed scalar/static aggregate ABI、Tagged Tuple v1 Option/payload-enum input、Bounded Array v1 canonical dynamic input、环境、hashed maps、LOG/revert、ETH、ERC-20/WETH/Uniswap/Permit closed calls | tagged/bounded return 与 aggregate storage 组合；dynamic constructor；call return/error 合同；缺少标准化资源/重入边界 |
| EVM SDK | `Storage.Layout` typed maps、Context/Immutable/Event/Revert/closed-call facade；`Access` owner/running gates 与 fixed single-pending two-step ownership | scalar/struct/fixed-array layout facade；bounded roles/reentrancy 与 token/NFT reusable components |
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
record/product/fixed-vector Borsh binding；R1-006 已完成 EVM canonical tuple/record/fixed-array
ABI binding；R1-007 已完成 SVM canonical Option/payload-enum tagged Borsh input binding；
R1-008 已完成 EVM Tagged Tuple v1 Option/payload-enum input binding；R1-009 已完成 SVM
fixed-capacity / canonical variable-length Borsh input binding；R1-010 已完成 EVM Bounded
Array v1 canonical dynamic input binding，以独立 `Evm.Codec.Emit` plan interpreter 处理
offset/length/tail/padding，不统一两个 target 的物理 layout，也不增加 array Ops 或 main-CFG
Emit recipe；R1-011 进一步用同一 static/tagged/bounded logical schema 固定两套 target plan
的 source projection conformance，但不统一 Borsh bytes 与 ABI words。下一切片进入 SVM-RT-1
bounded account view；并行的 R5-001 已先落地 Access
foundation：两个独立 contract 复用同一
owner/pause/two-step policy，pending owner 是一个 fixed Address 而不是 hashed map；详见
[R5-001](tasks/r5-001.md)。这不表示 R5 已完成。

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

R1-006 已完成 EVM static aggregate binding：`Evm.Codec` 独立选择 canonical tuple/record/
fixed-array selector type 与 one-word-per-scalar-leaf plan，IR 区分 logical schema 与 physical
word count，Emit 复用 canonical scalar guards/return packers，并输出标准 structured ABI JSON；
详见 [R1-006](tasks/r1-006.md)。

R1-007 已完成 SVM tagged input binding：`Svm.EntryAdapter` 独立选择 canonical Borsh u8 tag、
branch payload cursor、fixed local projection 与 inactive payload zeroing；一个 recursive codec
interpreter 覆盖普通 Lean Option 和 bounded UInt64-payload enum，不新增 Ops/Component/main
Emit case。Tagged return、bounded array 和 richer payload 继续 fail closed；详见
[R1-007](tasks/r1-007.md)。

R1-008 已完成 EVM tagged input binding：显式命名的 Tagged Tuple v1 将 `Option<T>` 绑定为
`(bool,T)`，将 bounded UInt64-payload enum 绑定为固定 `(uint8,p0,...)`；`Evm.Codec`
输入计划统一拥有 physical words、source projections、tag range 与 inactive-zero guards，IR、
generic guard renderer 和 structured ABI JSON 消费同一计划。它不复用 Borsh、不新增 Ops 或
type-specific Emit case；tagged return 和 bounded dynamic tail 继续 fail closed。详见
[R1-008](tasks/r1-008.md)。

R1-009 已完成 SVM bounded input binding：`Core.Value.BoundedVec α capacity` 的 host Vector
在 extraction 时擦除成 fixed scalar frame，SVM 以 recursive codec plan 绑定 canonical
Borsh `u32 length + active prefix`，清零 inactive locals 并要求 exact cursor consumption。
它不创建 target collection/pointer/heap state，也不新增 array Ops 或 main-Emit recipe；EVM
bounded dynamic ABI 仍独立 fail closed。详见 [R1-009](tasks/r1-009.md)。

R1-010 已完成 EVM bounded input binding：标准 ABI 暴露 `T[]`，但 `Evm.Codec` 将它绑定到
fixed `length + capacity × static element leaves` local frame；canonical offset、contiguous
tail、capacity、element padding 与 exact calldata 由 `Evm.Codec.Emit` 统一解释，inactive
locals 先清零。Dynamic constructor/return、nested dynamic 与 >64-word frame 继续 fail
closed；详见 [R1-010](tasks/r1-010.md)。

1. 已增加逻辑 `FixedBytes n`、`UInt128` 和 shared `UInt256` 的 source/profile 规则；fixed
   source limbs 不包含 target wire/account/storage geometry。
2. 定义 bounded codec schema：scalar、fixed bytes、tuple/record、enum、`Option`、固定/上限数组。
3. SVM adapter 实现 Borsh little-endian、canonical tagged/bounded input 与 exact cursor
   consumption；EVM adapter 实现 32-byte ABI word、static tuple、Tagged Tuple v1 与
   Bounded Array v1 canonical dynamic input。
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

R2-001 已完成 SRT-1：`Svm.AccountView.Source.View` 把 remaining-account 的 `base/capacity`
绑定为编译期句柄，运行时 index 统一经过 capacity、实际 `NUM_ACCOUNTS`、duplicate marker 与
header/data-length gate；按实际账户数定位 instruction data/program id，所有失败均在 state
store 前原子退出。该 view 只读、零拷贝，不持久化 pointer 或 runtime geometry。详见
[R2-001](tasks/r2-001.md)。R2 尚未完成；下一刀是 SRT-2 的 instruction/effects 与显式 scratch
区域合同。

### R3 — SVM SDK

SDK 按生命周期分两类，名字上也不能混：

- `AccountStorage`：持久 POD/Field、fixed Vec/Queue、ordered Map/RBMap、free-list allocator；
  descriptor 是编译期/抽取期 geometry，值是 account offset/index，不是 pointer。
- `Scratch`：invocation-local fixed/bounded Vec、byte writer、codec buffer；由 SVM bump allocator
  支撑，显式 capacity/OOM，离开 instruction 即失效。

`Account`、`Signer`、`Pda`、`System`、`Token`、`Token2022` facade 应直接组合已有
Runtime/Component，不增加“方便用”的 recipe opcode。Phoenix 用于证明复杂 orderbook 范式，
另外增加小型 Queue/Map examples，证明组件不是 Phoenix 专用品。

R3-001 已完成持久容器 foundation：`Svm.Sdk` 组合现有 checked account-storage effects，提供
POD Field、fixed Vec/Queue、ordered Map/RBMap、one-based allocator 和 canonical header
initialization。JobQueue/TicketLine 在独立 storage account 上复用这些组件；没有新增 Ops、IR、
Component 或 Emit recipe，也没有把 heap pointer、Lean `Array`/`Map` 放进持久状态。详见
[R3-001](tasks/r3-001.md)。R3 尚未完成；bounded transient Scratch 及 Runtime facade 仍依赖
R2 的 account/effect contracts。

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

R5-001 已完成 Access foundation：`Evm.Sdk.Access` 提供 owner/running gates 与固定
single-pending Address 的 two-step ownership；TwoStepCounter 和 Credits 独立复用它，替换
nominee 会立即使旧 nominee 失效，accept/cancel 显式清零。它没有 Access opcode、隐藏
storage write、hashed nomination namespace 或 magic guard。Roles、reentrancy 和 assets 仍受
上述 Runtime/storage 依赖约束；详见 [R5-001](tasks/r5-001.md)。

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
