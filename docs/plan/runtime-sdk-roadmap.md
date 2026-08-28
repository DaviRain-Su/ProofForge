# Runtime / SDK 双目标路线图

> 更新：2026-08-28。本文是 SVM 与 EVM 后续 Runtime / SDK 工作的权威排期；
> [backlog.md](backlog.md) 记录已经落地的证据和当前 Phoenix 切片。
> 多 agent 并行时的 write set、shared-lock 和交付合同见
> [并行开发执行图](parallel-workstreams.md)。
> “达到主流环境能力”的完整定义和 F0–F3 优先级见
> [mainstream parity baseline](mainstream-parity.md)。

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
| SVM Runtime | Loader-v3 ABI、编译期账户下标、PDA/seeds、sysvar、通用 CPI words、System/Token wrappers、typed scalar/static aggregate Borsh entry/return、Option/payload-enum tagged input、fixed-capacity canonical Borsh Vec input、bounded remaining-account view、typed CPI scratch/return-data 与 Token-2022 TLV envelope | tagged/bounded return policy；Token-2022 extension 完整语义 |
| SVM Component / SDK | `AccountStorage`、RBMap/allocator/cursor、recorder、FIFO cancellation；`Svm.Sdk` 已统一 fixed Account/Signer/bounded view、CPI-relative account handles、static ASCII PDA、non-seeded/generic ASCII-seeded System、classic Token fixed/role-typed signed transfer、fixed ATA CreateIdempotent/Memo、POD Field、fixed Vec/Queue、ordered Map/RBMap、one-based allocator、canonical initialization，以及 invocation-local heap buffer/fixed Vec/writer/signed-CPI codec plan | Rent-aware resize、general ATA/Memo、Token state/program-id policy 与 Token-2022 extension semantics 尚未统一；部分能力仍以具体 component 暴露；更高层 transient source collection lowering 仍 fail closed |
| EVM Runtime | Address/UInt128/UInt256/FixedBytes、typed scalar/static aggregate ABI、Tagged Tuple v1 Option/payload-enum input、Bounded Array v1 canonical dynamic input、环境、hashed maps、LOG/revert、ETH、ERC-20/WETH/Uniswap/Permit closed calls | tagged/bounded return 与 aggregate storage 组合；dynamic constructor；call return/error 合同；缺少标准化资源/重入边界 |
| EVM SDK | `Storage.Layout` typed maps、`Storage.Static` scalar/record/fixed-array declarations、Context/Immutable/Event/Revert；`Payments` bounded Ether/ERC20/WETH/fixed-router facade；`Access` owner/two-step ownership；`Roles.Set2` fixed-capacity membership/grant/revoke decisions；`Pausable` explicit fail-closed flag policy | typed pause events、reentrancy、code-existence/revert-bubbling policy 与 token/NFT reusable components；dynamic indexed Address return |
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
的 source projection conformance，但不统一 Borsh bytes 与 ABI words。SVM-RT-1 bounded
account view、R5-001 Access foundation、R5-002 static storage declarations、R5-003 bounded
roles、R5-004 Pausable policy 与 R5-005 bounded payment facade adoption 均已集成；独立 contract
分别复用这些 SDK contracts。
SVM-RT-2a 已把 CPI
instruction/scratch geometry 收口为 typed bounded plan；SVM-RT-2b 已继续统一
return-data/multi-seed signer-tail geometry；SVM-RT-3 第一刀已建立 Token-2022 bounded TLV
envelope，真实 extension 仍按语义分片开放。EVM-RT-2a 也已统一
closed CALL/STATICCALL result policy，EVM-RT-2b 已统一 typed LOG0..4/custom error，
EVM-RT-2c 已统一 payable/receive entry-value 与 calldata route policy，EVM-RT-2d 已统一
permit ecrecover 的固定 address/frame、STATICCALL success、exact returndata 与 nonzero
signer；UInt256 div/mod 也已固定 checked 零除 revert。下一刀继续剩余 R4 hardening。详见
[R2-001](tasks/r2-001.md)、[R2-002](tasks/r2-002.md)、[R2-003](tasks/r2-003.md)、
[R2-004](tasks/r2-004.md)、
[R4-001](tasks/r4-001.md)、[R4-002](tasks/r4-002.md)、[R4-003](tasks/r4-003.md)、
[R4-004](tasks/r4-004.md)、
[E-U256-004](tasks/e-u256-004.md)、[R5-001](tasks/r5-001.md)、[R5-002](tasks/r5-002.md)、
[R5-003](tasks/r5-003.md)、[R5-004](tasks/r5-004.md) 和 [R5-005](tasks/r5-005.md)。
这不表示 R2/R4/R5 已完成。

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

R2-001 已完成 SRT-1：现由 `Svm.Sdk.Account.View` 拥有的 remaining-account `base/capacity`
绑定为编译期句柄，运行时 index 统一经过 capacity、实际 `NUM_ACCOUNTS`、duplicate marker 与
header/data-length gate；按实际账户数定位 instruction data/program id，所有失败均在 state
store 前原子退出。该 view 只读、零拷贝，不持久化 pointer 或 runtime geometry。详见
[R2-001](tasks/r2-001.md)。R2 尚未完成；其后的 SRT-2a layout foundation 如下。

R2-002 已完成 SRT-2a layout foundation：`Svm.Scratch` 用 invocation-only bank、aligned
region allocator 和 typed `InstructionPlan` 统一 static invoke 与 dynamic signed self-CPI 的
metas/descriptor/data/infos/signer-tail geometry；malformed bank、重复 region、非法 alignment 与
1,024-byte CPI bank OOM 都在发射前失败。plan 只含编译期 byte counts，不含 pointer/account
offset，也没有新增 Ops/IR/Component/Emit recipe。该 foundation 当时尚未覆盖 return data 与
multi-seed composition；详见 [R2-002](tasks/r2-002.md)。

R2-003 已完成 SRT-2b：`SignerSeedTail` 统一 ordinary invoke / dynamic signed self-CPI 的
copied bytes、aligned bump、seed-entry array 与 signer group；`ReturnDataStaging` 统一固定
32-byte program id + 8-byte payload。所有 geometry 经同一个 invocation-only `Plan.alloc`
做 alignment/OOM gate，现有 assembly 不变；不开放 dynamic return data、runtime pointer 或
persistent heap object。详见 [R2-003](tasks/r2-003.md)。

R2-004 已完成 SRT-3 的 bounded envelope foundation：`Svm.Cpi.TokenTlv` 从 pinned SPL
interface 固定 base/padding/type/TLV geometry，host reference cursor 用 UInt64 offset/count 与
28-bit duplicate bitmap 验证 bounded advance；generated closed specialization 不分配 heap、
不持久化 pointer，并由证明化的 straight-line interpreter 接受 classic base 和 official
end/padding form。所有真实 extension 继续 fail closed，transfer-fee/hook 等必须在后续切片
连同完整账户和 CPI 语义单独开放；详见 [R2-004](tasks/r2-004.md)。R3 的 seeded
System、Token state/program-id policy 与 Token-2022 extension facade 仍未完成。

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
[R3-001](tasks/r3-001.md)。R3-002 继续提供 compile-time fixed Account/Signer handles，并把
bounded remaining-account view 移入同一 SDK owner；Trio 与 AccountView 独立消费，旧
`AccountView.Source` 不再保留第二套 API。既有 account leaves 只接受 compiler-proven static
index，runtime account geometry 仍 fail closed；详见 [R3-002](tasks/r3-002.md)。R3-003 又直接
复用 `Heap.State`、`Scratch.Plan` 与既有 invocation-only lifetime，提供 bounded heap buffer、
fixed vector、byte writer 和 signed-CPI codec composition；BatchRecorder/CPI 两个真实 consumer
保持产物逐字节不变，没有平行 allocator/plan 或持久 pointer；详见
[R3-003](tasks/r3-003.md)。R3-004 再提供 `Svm.Sdk.Pda.Ascii` 与 `Svm.Sdk.System` 的
static/fixed-account foundation；Pda、Transfer、Create、CreatePda 只消费 SDK 名称，通用
`pf_inline` Runtime 展开保持四个程序的 canonical IR 和产物不变，单 seed ASCII policy
在 IR verifier fail closed；详见 [R3-004](tasks/r3-004.md)。R3-005 已把 non-seeded System 的
assign/allocate/advanceNonce 补入同一 facade，SysAlloc/Nonce 保持 canonical IR 和产物不变；
详见 [R3-005](tasks/r3-005.md)。R3-006 已统一 classic Token 的 fixed facade，并以
`CpiAccount.Handle` 和 role-typed checked/unchecked transfer descriptor 收敛 Phoenix 的重复
positional account lists；应用仍在 `Examples` 拥有具体布局，全部相关产物不变，详见
[R3-006](tasks/r3-006.md)。R3-007 又把 fixed ATA
`CreateIdempotent` 与 fixed Memo 移到 `Svm.Sdk.AssociatedToken` / `.Memo`，显式保留
caller-selected Token program 和 bounded-data/program-id 缺口；Ata/Memo 产物不变，详见
[R3-007](tasks/r3-007.md)。R3-008 又提供 `Svm.Sdk.System.AsciiSeed` 的 generic compile-time
ASCII allocate/create/assign/transfer；seed length 由 SDK 自动编码，verifier 对四种 closed
System geometry 校验 1–32 ASCII bytes 和相邻 bincode length，SysSeed/SysXfer 产物不变，详见
[R3-008](tasks/r3-008.md)。R3 尚未完成；rent-aware resize、general ATA/Memo、Token
state/program-id policy 与 Token-2022 extension semantics 仍待完成。

### R4 — EVM Runtime

1. ABI：`uint8..256`、address、fixed bytes、tuple/record、fixed array 和有上限的 calldata bytes；
   selector、calldata 长度、offset、padding 全部 fail closed。
2. Storage：scalar/struct/fixed array 静态 cursor 与 typed hashed map；布局在抽取期确定，禁止
   运行时 slot allocator。
3. Effects：完整环境 read、LOG0..4 的 typed plan、custom errors、receive/payable、closed
   CALL/STATICCALL 的 success/return-data contract。
4. arithmetic：UInt256 compare/bitwise/div/mod 和明确 overflow policy；不把 UInt64 默认规则
   偷套到 EVM word。

EVM-SDK-2 / R5-002 已完成 Storage 子切片：`Evm.Sdk.Storage.Static` 提供 extraction-time
scalar、Address/wide、flat record、fixed array 与 record-array cursor/typed handles；两个独立
contract 的普通 typed State flattening 与 declaration leaf table 逐槽一致，并由 Anvil 直接
核对 constructor、targeted mutation、邻槽保持、OOB 与权限原子失败。描述符不生成 runtime
allocator，也不改变 hashed-map namespace 或增加 Ops/IR/Component/Emit recipe；详见
[R5-002](tasks/r5-002.md)。

R5-003 已在 static declaration 之上提供 `Roles.Set2`：capacity 2 的两个显式 Address slot
只做 membership/vacancy/grant/revoke slot 决策，两个 consumer 自己拥有权限、terminal 与
literal field write。没有 persistent SDK object、Vector、hashed role map、runtime allocator
或 target recipe；indexed Address return 因 OOB-zero extraction 尚不可靠而继续 fail closed。
详见 [R5-003](tasks/r5-003.md)。

R5-004 已把 pause policy 从 Access 拆为 `Evm.Sdk.Pausable`：canonical u8 flag、fail-closed
predicate 与 replacement transition 统一归属 SDK，consumer 自己拥有权限、事件和显式 State
field write。抽取器只补齐通用 narrow-scalar `pf_inline` 展开，没有 Pausable 名字或 target
recipe；TwoStepCounter/Credits 的 Yul/ABI/bin 保持逐字节一致。详见
[R5-004](tasks/r5-004.md)。

R5-005 已把已有 Ether/ERC20/WETH/fixed-router facade 从 Base 拆为独立
`Evm.Sdk.Payments` owner，并让 Vault、TipJar、Ownable 只 import contract-facing `Evm.Sdk`。
所有 CALL/STATICCALL/payable/result semantics 仍由现有 Runtime/Component contract 拥有，三个
program 的 IR 与九份 Yul/ABI/bin 逐字节不变；详见 [R5-005](tasks/r5-005.md)。

R4-001 已完成 EVM-RT-2a typed call-result contract：`Evm.CallResult` 统一 success-only、
exact-one-word 与 ERC-20 empty-or-nonzero-word policy，最多复制 32 bytes returndata；
`ClosedCall.Emit` 的 transfer/approve/permit/balance/allowance/WETH/router paths 统一消费该
interpreter，产物保持 byte-identical。callee/calldata 仍由 closed vocabulary 拥有，没有开放
arbitrary call、delegatecall/create 或隐藏 allocation。R4 的 typed LOG0..4/custom-error plan
在下一切片完成；详见 [R4-001](tasks/r4-001.md)。

R4-002 已完成 EVM-RT-2b typed LOG/custom-error plan：`Evm.LogError` 以有界 plan 统一
LOG0..4 topic count/data offsets/data length，以及 lowercase 4-byte selector/argument offsets/
revert length；NativeFx 和 permit 的 closed semantic consumers 全部消费唯一 interpreter，20 个
合约的 Yul/bin/ABI 保持逐字节一致。它没有开放 arbitrary event/error/opcode，也不引入 runtime
allocator；详见 [R4-002](tasks/r4-002.md)。

R4-003 已完成 EVM-RT-2c payable/receive policy：`Evm.Payable` 以 typed value gate、calldata
route 和 validated entry plan 统一 constructor/runtime/selector nonpayable rejection、deposit
exact CALLVALUE、receive accept-any binding、empty-calldata receive 与 selector dispatch；
malformed gate/route/operand shape 在唯一 interpreter 内 fail closed。source API、IR/digest、
ABI payable labels 与 20 个合约产物保持逐字节一致；native send CALL 继续归 closed
NativeFx/CallResult policy。详见 [R4-003](tasks/r4-003.md)。

R4-004 已完成 EVM-RT-2d typed closed ecrecover contract：`Evm.Precompile.Plan` 固定唯一
precompile address `0x01`、128-byte input frame、32-byte output 与 success/exact-size/nonzero
三道门，`ClosedCall.Emit` permit 只消费唯一 interpreter。exact returndata gate 防止 invalid
ecrecover 以空 returndata 成功时把 output memory 的旧输入误认成 signer。只有 Token Yul/bin
发生预期变化；其他产物、全部 ABI 与 IR digests 保持不变。它不开放其他 precompile、
arbitrary STATICCALL、delegatecall 或 create。详见 [R4-004](tasks/r4-004.md)。

E-U256-002 已完成 unsigned compare 子切片：`WideWord.Comparison` 和唯一 component emitter
覆盖 eq/lt/le/gt/ge，SDK 不再要求合约拼 limbs 或写 Yul relation；原 `ge256` canonical
spelling 保留，因此 Token/Capped 等既有 IR/产物不漂移。Wide 的跨 64/192-bit Anvil matrix
验证五种 relation；E-U256-003 已在同一 component 加入 typed bitwise/shift，E-U256-004
继续加入 checked div/mod，并在 Yul operation 前统一拒绝零 divisor。详见
[E-U256-002](tasks/e-u256-002.md)、[E-U256-003](tasks/e-u256-003.md) 和
[E-U256-004](tasks/e-u256-004.md)。

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
storage write、hashed nomination namespace 或 magic guard。详见 [R5-001](tasks/r5-001.md)。

R5-002 已完成 compile-time static storage declaration foundation。它给后续 roles、asset
records 和 fixed collections 提供可验证 handles，但当前 runtime 访问仍由普通 typed State
field extraction 拥有；不能把 descriptor 当成隐藏 `sload`/`sstore` API。EVM-RT-2 完成前，
reentrancy 与 arbitrary-call-dependent policy 继续 fail closed。

R5-003 已完成 bounded static roles：`Roles.Set2` 封装固定两个 Address slot 的纯策略判断，
EvmStaticCounter/EvmStaticRoster 用不同权限和业务策略组合它，并保持每个 storage write 显式。
动态角色集合、indexed Address return、reentrancy 与 assets 仍 fail closed。

R5-004 已完成独立 Pausable policy：canonical u8 flags、fail-closed predicates 和 replacement
transitions 由 SDK 所有，TwoStepCounter/Credits 保持权限与显式 field write。typed pause events
仍等待 generic event surface；ReentrancyGuard 必须先证明 lock write → external CALL → clear 的
effect ordering，不能用普通 returned State 冒充。

R5-005 已完成 bounded payment facade adoption：Ether/ERC20/WETH/fixed-router source names 归
`Evm.Sdk.Payments`，Vault/TipJar/Ownable 不再 import target Runtime 或 lower Source modules，
同时保持 canonical IR 和 artifacts。它没有把 closed call 扩成 arbitrary calldata，也没有
声称 code-existence、revert bubbling 或 reentrancy 已完成。

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
