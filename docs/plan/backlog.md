# Backlog

补全依据：[analysis/authority.md](analysis/authority.md)。
缺口阶段：[analysis/gap-vs-proofforge.md](analysis/gap-vs-proofforge.md)。
后续权威排期：[Runtime / SDK 双目标路线图](runtime-sdk-roadmap.md)。
主流能力目标：[Solana SDK / Solidity + OpenZeppelin parity baseline](mainstream-parity.md)。

双目标路线固定为 `R0 ownership → R1 shared protocol values → R2 SVM Runtime →
R3 SVM SDK → R4 EVM Runtime → R5 EVM SDK → R6 cross-target hardening`。共享普通 Lean、
Profile、Extract 和 Core CFG；SVM account geometry 与 EVM storage layout 各归 target 所有，
不做虚假的统一 storage。R0 ownership freeze 已完成；R1-001 已固定 typed scalar metadata、
bounded codec descriptor/resource budget，并把 EVM selector/calldata guard/ABI 从 width
sentinel 迁到 `Evm.Codec`。R1-002 source slice 已加入 allocation-free shared
`FixedBytes n` / u128/u256 并由 Extract 推导固定 limb metadata；R1-003 已分别绑定 SVM
exact-cursor Borsh 与 EVM u128/bytesN ABI，不把 codec geometry 混入 account/storage；
R1-004 已从普通 Lean 推导 bounded tuple/record/enum/option/literal-Vector schema，并贯穿
Core/SVM/EVM IR；R1-005 已由 SVM 独立绑定 static record/product/fixed-vector Borsh；
R1-006 已由 EVM 独立绑定 canonical tuple/record/fixed-array ABI；R1-007 已由 SVM 独立绑定
普通 Lean Option/payload enum 的 canonical tagged Borsh input；R1-008 已由 EVM 独立绑定
Tagged Tuple v1 `(bool,T)` / `(uint8,p0,...)` input policy；R1-009 已由 SVM 独立绑定
compile-time capacity + canonical Borsh `u32 length` input；R1-010 已由 EVM 独立绑定
canonical standard-ABI dynamic head/tail 与 fixed local frame；R1-011 已用同一 logical
static/tagged/bounded schema 对照两套 target plan 的 source projections，同时保持 Borsh
cursor、ABI offset 与 target 物理编码互相独立；R1-012 已为 shared `BoundedVec` 增加
capacity-preserving 操作语义，并让 scalar runtime-index read 经两套 target codec adapter
组合成既有 bounded select，不新增集合 opcode；R1-013 已建立不含 host HashMap/pointer 的
bounded Map/Set logical contract，物理 binding 继续由两个 target 各自所有。SVM-RT-1
bounded account view 与 EVM-SDK-2 static storage declarations 已并行集成；SVM-RT-2a 已完成 typed bounded
instruction/scratch layout；SVM-RT-2b 也已把 return-data 与 multi-seed signer tail 收口到
同一个 bounded plan；SVM-RT-3 第一刀已用 allocation-free scalar cursor/bitmap 建立
Token-2022 TLV envelope，并继续对所有未建模 extension fail closed；R2-005 已把官方四个
program-memory syscall 绑定为 checked account spans，pointer 只在 host call 边界瞬时存在。
R2-006 已把 remaining compute、invocation stack height 与两个 allocation-free numeric logger
收口到 target-owned Telemetry Query/Call，并继续只经过 generic Component bridge。
EVM-RT-2a typed call-result 已完成，
EVM-RT-2b 已统一 typed LOG0..4/custom-error plan，EVM-RT-2c 也已统一 payable/receive
entry-value 与 calldata route policy，EVM-RT-2d 已把 permit 的固定 ecrecover address/frame、
STATICCALL success、exact returndata 与 nonzero signer 收口到 typed closed contract；UInt256
div/mod 已固定 checked 除零 revert 策略；EVM-RT-2e 已加入 schema-resolved ordered static
UInt64 store，为 CALL 前后可见的 lock effect 提供 sound foundation；R4-006 已补齐 full-width
gas/basefee/prevrandao/gaslimit 并钉死 Cancun opcode 语义；R4-007 已让所有 source
`.errorNamed` 叶自动进入 zero-argument custom-error ABI metadata；R4-008 已把 production
full-width environment lowering 收口到 generic Component bridge；R5-009 已在其上组合
reusable ReentrancyGuard policy。并行 EVM
UInt256 线现已补齐 typed comparison/bitwise/shift/div/mod。
并行 SDK 线已完成 R3-001 persistent SVM foundation、R3-002 Account/Signer facade、
R3-003 invocation-local transient SDK、R3-004 static PDA/System facade foundation、
R3-005 non-seeded System facade completion、R3-006 classic Token facade、
R3-007 fixed ATA/Memo facades、R3-008 generic seeded System facade、
R3-009 bounded static Memo facade、R3-010 general ATA facade、
R3-011 canonical program-id / SPL Token base-state views、R3-012 source-visible transient Vector64、
R3-013 source-visible transient bounded bytes/writer、
R3-014 stable Clock/EpochSchedule/Rent SDK facade、
R3-015 shared transient lifecycle emitter、
R3-016 bounded transient log-data binding、
R5-001 EVM Access foundation、R5-002 EVM static storage foundation、
R5-003 bounded static roles、R5-004 Pausable policy、R5-005 bounded payment facade adoption 与
R5-006 fungible debit ledger foundation、R5-007 checked credit/alias-safe transfer、
R5-008 checked allowance core、R5-009 reusable reentrancy policy、
R5-010 persistent bounded EVM storage vector；
这些都是阶段内可复用组件切片，不代表 R3/R5 整体完成。
R0-002 已把“达到主流环境能力”固定为 shared bounded language、target Runtime 和 reusable
SDK policy 三层，并按 F0 shared substrate、F1 Runtime、F2 policy、F3 lifecycle 排序；详见
`docs/plan/tasks/r0-002.md`。Vector/Map/allocator 必须分别声明 boundary、invocation-local、
SVM account-persistent 或 EVM storage-persistent 生命周期，不能再用同名 host 类型代替能力证明。

## 已做

- **当前可验证基线（2026-08-29）**：Lean 汇总 326 jobs；SVM manifest 全 56 programs；
  Mollusk 全量 322/322（Phoenix-v1 profile 76/76、RawEntry 20/20）；EVM manifest 全
  20 programs 且 Anvil 20/20。CI 将 SVM / EVM 分成独立并行 lane，并保留汇总 `test` gate；
  一个 target 失败不再跳过或延迟另一个 target 的反馈。
  solc 0.8.34 的 Token Yul `StackTooDeepError` 已由共享 runtime address encoder 修复，
  当前 Token deployment bytecode 为 19,348 B；Surfpool 1.5.0 部署门见 P5 最新记录。
- S0–S5：普通 Lean Counter 竖切到 Mollusk
- 多字段 UInt64；从 `init` 返回 structure 收字段；Pair `.so` / Mollusk 4/4
- Loader 偏移按 `dataLen` 算
- `@[pf_entry]` + `#pf_build`；按名 disc；Counter 同程序 decrement
- 任意 `ite`；checked mul/div/mod；`=` `≠` 比较；Counter scale/divide/modulo/nonzero
- `IR.digestHex`（FNV-1a 64）；`#pf_build` 抽出与 fixture 必须同一 digest
- 带类型字段表：`UInt8/16/32/64` + `Option UInt64` 双叶；Flag / Maybe Mollusk
- disc / layout marker 本机 SHA-256，不再挂名表
- 定长 `Vector UInt64 n` 展开成连续槽；Window Mollusk；不定长 Array fail closed
- 无 payload 枚举作 tag；Phase Mollusk；带 payload 仍 fail closed。Bool 已在 L4-034 开成 1 字节 u8-le
- 多个 init；`init` paramCount 按 λ 算；Pair `initBoth` / `getRight`
- `Option UInt64` match 读 payload；Maybe.getValue Mollusk
- 单字段用户 inductive 作 tag+payload；Choice Mollusk
- `clockSlot` + 账户 0 `signerKey0`；Clock Mollusk
- 封闭 `system.transfer`；三账户虚地址 walk + `sol_invoke_signed_c`；Transfer Mollusk
- 编译期钉死的 `invoke`；`systemTransfer` / `invokeAcc1` 共用发射器；Ping Mollusk
- 账户 0 AccountInfo 只读叶子（lamports / owner 首 u64 / data_len / NUM_ACCOUNTS / 三旗）；Info Mollusk
- 表层通用 `invoke`；`systemTransfer` / `invokeAcc1` 是普通包装；Call Mollusk
- `findPda` 一条 ASCII 种子 + 当前 program id；返回 bump；Pda Mollusk
- `invokeSigned` 一组 ASCII 种子 + bump；Signed Mollusk（错 bump 失败）
- `systemCreate` 普通包装；owner = 当前 program id；Create Mollusk
- `tokenTransferChecked` 普通包装；Token `TransferChecked`；TokenXfer Mollusk
- `ataCreateIdempotent` 普通包装；ATA CreateIdempotent；Ata Mollusk
- `rentExemption` 叶子；`sol_get_rent_sysvar` × `(128+n)`；Rent Mollusk
- `tokenMintToChecked` / `tokenBurnChecked`；TokenMint Mollusk
- `systemAssign` / `systemAllocate`；SysAlloc Mollusk
- `tokenInitAccount` / `tokenCloseAccount`；TokenAcc Mollusk
- `memoWrite`；Memo Mollusk
- `createPda`；CreatePda Mollusk
- `checkPda`；Pda Mollusk 验证 bump
- `tokenApproveChecked` / `tokenFreezeAccount` / `tokenThawAccount`；TokenApprove / TokenFreeze Mollusk
- `clockEpoch`；Clock Mollusk 两次 warp 跨 epoch
- `tokenSetMintAuthority` / `tokenRevoke`；TokenAuth Mollusk
- `slotsPerEpoch`；Epoch Mollusk 改 schedule
- `tokenAccountSize` / `cpiReturn`；TokenSize Mollusk 返回 165
- `systemAllocateWithSeed`；SysSeed Mollusk
- `systemCreateWithSeed`；SysSeed Mollusk 转 lamports
- `systemAssignWithSeed`；SysSeed Mollusk 改 owner
- `systemTransferWithSeed`；SysXfer Mollusk
- `tokenInitMint`；TokenMint2 Mollusk
- `tokenSyncNative`；TokenNative Mollusk
- 账户 1 只读叶子；Peer Mollusk
- `sha256Lit`；Hash Mollusk
- 32B key / owner 按字读；Keys Mollusk
- `keccak256Lit`；Keccak Mollusk
- 账户下标叶子收口；Trio Mollusk
- Bool / `unixTime` / nonce prelude / SetAuthority owner / Approve / Multisig2；Gate / Nonce / TokenOwner / TokenMs Mollusk
- Core control/schema 与 `Svm.Ops/IR/Runtime`、`Evm.Ops/IR/Runtime` 分层；Extract.IR 是唯一 typed target-extension 组合点
- 嵌套 structure / `Vector Nested n` 摊平；Nested / Tree Mollusk
- Phoenix bounded N=4 双边书、四 seat registry、逐 seat 结算、TIF、费用和 typed event batch
- SVM 异构 PDA seeds（ASCII/state key/account key）、完整 canonical key 校验和可续接 ignored CPI；Phoenix classic SPL Token 双 vault 全链路
- SVM packed u8/u16/u32/u64 CPI words 与 canonical PDA 签名 raw self-entry；SelfLog 覆盖 self-CPI、续段写回和认证失败矩阵
- Phoenix 官方形状 `AuditLogHeader` / Borsh event 通过 `"log"` PDA signed self-CPI 发布真实 `Program data`
- SVM 51 个 registry program 各有 runtime test 文件；EVM 15 个 registry program 全进 Anvil 总入口
- 审查修复：分支 fallthrough、state owner/marker、常量求值、Option identity、窄叶、Nat.sub、移位、EVM init、未知 CPI、solc 诊断
- GitHub CI 串行执行 Lake guards、51 个 SVM 构建 + Mollusk，以及 15 个 EVM 构建 + Anvil
- Core 显式 basic-block CFG 第一阶段：block arguments、显式 branch/checked/exit、完整 checker、local CSE、线性共享 block；Phoenix 全方法已通过 lowering/validation
- SVM/EVM emitter 已消费 target-owned Core CFG：SVM 用全局 block layout + 迭代 long-jump relay，EVM 用 Yul `pf_pc` dispatcher；当时 Phoenix 汇编由 4,109,725 B 降至 2,748,784 B（加入 trader topology 后当前为 3,314,430 B），全部 49 个 Mollusk 文件与 12 个 Anvil 程序通过
- Solanalib CFG correspondence：Counter add/sub/mul/div/mod 的 Core operands / physical slot / success-overflow edge 必须一致；typed guards、multiply zero-path jump、`r10-24` scratch handoff、static store 由上游 small-step semantics 执行。普通 eq/ne/lt/le/gt/ge branch 保留 cmp/operands/then/else identity，exact decoded pair theorem 证明 edge selection 与内存不变
- 通用 target registration：`Core.Target.Registration` 统一递归投影公共 Val/Op/Program，并携带 extension callbacks、arity、op well-formedness 和 CFG dialect；SVM/EVM conversion 已移回各自 IR，`Extract.IR` 不再含后端 projection case。Core-only 合成第三 target 证明新增公共语言后端无需修改抽取 IR，并继续 fail closed 拒绝 foreign extension
- Token-2022 classic-compatible `TransferChecked`：通用 `CpiMeta.expectedDataLen` 在 CPI 前约束 base Mint=82B / Account=165B；真实 base transfer 成功，transfer-fee / enabled transfer-hook mint 原子拒绝；Runtime CPI wrapper 改为按命名空间统一展开，不再维护 recipe 名白名单
- 独立 Tree N=4 删除切片：successor transplant、全部可达 delete-fixup、free-list 回收和精确地址复用；24 种插入顺序 × 4 个删除 key 的宿主不变量门，以及 black-leaf fixup/reuse Mollusk 链上门
- Phoenix trader tree 持久化 N=4 topology：root/left/right/parent/color、bounded 插入/删除修复和 exact address reuse；deposit 沿 links 查找并复用 parent，evict 先 detach 再回收。抽取器只增加 target-neutral 的 continuation/conditional-state/vector-write lowering，没有 Tree/Phoenix 名字或 emitter 特判
- Phoenix ask/bid order tree 持久化 N=4 topology：payload 地址稳定，撮合按中序 best/successor 遍历，fill/expiry/reduce/cancel detach，满书驱逐后 exact address reuse。通用抽取器增加 scalar let zeta-reduction 和 qualified nested-vector schema path；两个 target emitter、IR 与 Phoenix ABI 无需特判或改动

## 当前状态

- R1-001 typed codec foundation 已完成：`Core.Codec` 提供 bool/uint/address/fixed-bytes 与
  unit/tuple/record/enum/option/fixed/bounded array logical shape，并以 depth/nodes/leaves/
  capacity 做 fail-closed 资源预算。Extract → Core.Target → SVM/EVM IR 透传
  `paramTypes`/`retTypes`；EVM selector、word guard、wide carrier 和 ABI JSON 消费 typed
  metadata。历史 `1/2/4/8/20/32/33` 只在 `Evm.Codec` compatibility boundary 恢复旧
  Golden/Legacy fixture，`Crypto.Keccak` 和 production `Evm.Emit` 不再解释这些 sentinel。
  这不是 aggregate codec 完成声明：SVM RawEntry 仍未从任意 descriptor 自动生成 Borsh。详见
  `docs/plan/tasks/r1-001.md`。本切片最终门：Lean Tests 236 jobs、SVM 51 programs、locked
  Mollusk 285/285、EVM 15 programs、Anvil 15/15；ownership、whitespace、Markdown link 与
  production Emit width-sentinel static guards 全绿。SVM ELF 未改变，因此不重复 Surfpool
  部署门。

- R1-002 allocation-free source-values slice 已完成：`Core.Value` 以固定 UInt64 limbs 提供
  shared `UInt128` / `UInt256` / literal `FixedBytes n`（`1 ≤ n ≤ 32`），不包含 Array、Map、
  heap buffer 或 pointer。Extract 推导 typed metadata 与 2/4/`ceil(n/8)` return limbs；
  非 literal、0-byte、33-byte 形状 fail closed。EVM 旧 UInt256/Bytes32 名保留为兼容 alias，
  ABI 与 storage 物理布局仍由 target 所有。这仍不是 target codec 完成声明：下一片才做
  SVM exact-cursor Borsh、EVM u128/left-aligned bytesN guards/returns 和 cross-target fixture。
  详见 `docs/plan/tasks/r1-002.md`。

- R1-003 scalar target-adapter slice 已完成：SVM 从 typed metadata 推导 logical binder 到
  fixed physical leaves 的映射，以 exact little-endian Borsh cursor 解码/返回 `UInt128` 与
  partial-limb `FixedBytes 12`，short/trailing input 和 bare multi-limb scalar use 均 fail
  closed；不分配 heap buffer，不把 pointer 写入 account。EVM 分别按 numeric right-aligned
  uint128 与 source-order left-aligned bytesN ABI 解码，拒绝 noncanonical high bits/right
  padding，并以 bounded runtime helper 返回 bytesN、重打包 permit bytes32。Profile 只放行
  literal valid `FixedBytes n` metadata，继续拒绝 runtime/polymorphic `Nat`。RawEntry digest
  `83dda49b07d85f48`、ELF 12,048 B，并由 Surfpool 1.5.0 以 12 个 Loader-v3 writes 部署；
  Wide digest `692687089d4455f3`，Token digest `4f1db71eb59d4254`。237-job Lean、51 个 SVM
  build、Mollusk 286/286（RawEntry 12/12）、15 个 EVM build 与 Anvil 15/15 全绿。详见
  `docs/plan/tasks/r1-003.md`。后续 R1-004 已完成 bounded aggregate source metadata；
  两者都不统一 SVM account geometry 与 EVM storage layout。

- R1-004 aggregate source-metadata slice 已完成：Extract 从 Bool/scalar、Unit、`Prod`、
  non-polymorphic record、bounded non-recursive enum、`Option` 与 literal-length `Vector`
  推导并预算校验 `Core.Codec.Schema`；Method 以 `paramSchemas` / `retSchema` 贯穿
  Core.Target 和 SVM/EVM IR，effectful return 只暴露 `Except Error (State × Result)` 的
  `Result`。aggregate 不再回退成假的 `.uint64`；两个 target 在独立 codec adapter 落地前
  显式拒绝 aggregate 参数。动态 Array、递归、inheritance、polymorphic 与 over-budget
  shape 在 emission 前 fail closed；本切片未扩 Ops/Component/Emit。详见
  `docs/plan/tasks/r1-004.md`。

- R1-005 SVM static aggregate Borsh slice 已完成：`Core.Codec.staticLeaves` 只提供 typed
  source-order logical path；`Svm.EntryAdapter` 独立选择 little-endian widths、fixed scalar
  local ranges 与 canonical Bool guard。普通 Lean nested record、`Prod`、literal `Vector`
  projection 在 SVM IR 投影后绑定到已解码 local，不创建 aggregate heap object、不把 pointer
  写入 account，也不新增 Ops/Component/main-Emit case。`RawEntry.aggregate` 的 exact 29-byte
  Borsh wire 与 malformed Bool/short/trailing 负例进入 Mollusk；Option/enum/bounded-array tag/
  length policy、generated aggregate SVM ABI 与 EVM aggregate ABI 仍 fail closed。RawEntry digest
  `256081fbe6a93fcc`、ELF 13,624 B，经 Surfpool 1.5.0 的 14 个 Loader-v3 writes 部署核对；
  Lean 237、SVM 51 builds、Mollusk 287/287（RawEntry 13/13）、EVM 15 builds、Anvil 15/15、
  ownership/whitespace 全绿。详见 `docs/plan/tasks/r1-005.md`。

- R1-006 EVM static aggregate ABI slice 已完成：共享层新增 target-neutral 的 typed static
  projection resolver 和可复用 fallible value/operation rewrite traversal；`Evm.Codec` 独立
  选择 canonical tuple/record/fixed-array selector spelling 与 one-word-per-scalar-leaf plan。
  EVM IR 区分 logical parameter count 和 physical ABI word count，Emit 对每个摊平叶复用既有
  Bool/narrow/address/fixed-bytes canonical guard、支持 wide/fixed-bytes/address aggregate
  result packing，并在 ABI JSON 保留 tuple components/fixed-array shape。`EvmCtx.aggregate`
  用普通 Lean nested record、`Prod`、literal `Vector` 验证 exact 260-byte calldata、8 个物理
  words、`(uint64,bool)` return 与 malformed Bool rejection；Option/enum/bounded-dynamic policy
  继续 fail closed。EvmCtx digest `856b382fd7f7552`，deployment bytecode 541 B；Lean 237、
  SVM 51 builds、Mollusk 287/287、EVM 15 builds、Anvil 15/15、ownership/whitespace 全绿。
  详见 `docs/plan/tasks/r1-006.md`。

- R1-007 SVM tagged Borsh input slice 已完成：`Svm.EntryAdapter` 从普通 Lean Option/enum
  schema 生成 reusable sequence/scalar/option/enum decode tree、fixed invocation-local slots、
  logical projections 和 min/max wire bound；codec backend 用一个 recursive exact-cursor
  interpreter 处理 canonical u8 tag、branch payload、inactive slot zeroing、short/trailing
  rejection。SVM IR 在 Core CFG 前把 tagged projections 绑定到 local；没有新增 Ops、
  Component 或 main-Emit case，没有 heap/account pointer。Extract 只在 Option payload 参与
  后续计算时物化 local，因此旧 Maybe/Choice digest/产物不漂移。RawEntry 普通 Lean
  `Option UInt64` 与 0/1/2-payload enum 覆盖合法分支、bad tag、short/trailing 负例；tagged
  return、bounded array 与 richer enum payload 仍 fail closed。RawEntry digest
  `5fde6b9cfc767c10`、ELF 16,816 B；Lean 237、SVM 51 builds、Mollusk 288/288（RawEntry
  14/14）、EVM 15 builds、Anvil 15/15、Surfpool 1.5.0 Loader-v3 exact bytes、ownership/
  whitespace 全绿。详见 `docs/plan/tasks/r1-007.md`。

- R1-008 EVM Tagged Tuple v1 input slice 已完成：`Evm.Codec.AbiInputPlan` 对普通 Lean
  Option 选择 fixed `(bool,T)`，对 bounded UInt64-payload enum 选择 fixed
  `(uint8,p0,...)`，并统一描述 physical words、source projections、tag range 与每个 variant
  的 active payload prefix。EVM IR 在 Core CFG 前完成 logical→physical rewrite；Emit 只用
  generic guard renderer 拒绝 noncanonical Bool/out-of-range tag/absent payload/inactive lane，
  ABI JSON 输出命名 tuple components。它不复用 branch-dependent Borsh，不新增 Ops、Component
  或 type-specific Emit case。`Examples.EvmCtx` 覆盖 Option 与 0/1/2-payload enum 的所有
  合法分支和 malformed calldata；tagged return、bounded dynamic 和 richer enum payload 仍
  fail closed。EvmCtx digest `da71408333a778a6`、deployment bytecode 1,062 B；详见
  `docs/plan/tasks/r1-008.md`。

- R1-009 SVM bounded Borsh input slice 已完成：共享 `Core.Value.BoundedVec α capacity`
  只携带 runtime `UInt32` length 与 compile-time/source-only `Vector`；Extract 要求 literal
  capacity，并在 target emission 前把全部元素摊平成 fixed scalar projections。SVM 独立选择
  canonical Borsh `u32 length || length elements`，recursive plan interpreter 检查
  `length ≤ capacity`、预先清零未使用元素、只解码 active prefix，并用 exact final cursor
  拒绝 short/trailing bytes。它不新增 array Ops、Component 或 main-Emit recipe，不产生 target
  collection header、heap allocation、account pointer 或 persistent Map/Array。EVM bounded
  dynamic ABI 继续 fail closed。RawEntry digest `101c1601217390a4`、ELF 18,240 B；Lean 237、
  SVM 51 builds、Mollusk 289/289（RawEntry 15/15）、EVM 15 builds、Anvil 15/15、Surfpool
  1.5.0 Loader-v3 exact bytes、ownership/whitespace 全绿。详见
  `docs/plan/tasks/r1-009.md`。

- R1-010 EVM bounded ABI input slice 已完成：同一 `BoundedVec` 在 EVM 上绑定为标准 `T[]`
  dynamic head/tail，但 target frame 仍是 `length + capacity × static element leaves`。Codec
  plan 固定 canonical contiguous offsets、capacity、element words 与 source projections；独立
  `Evm.Codec.Emit` interpreter 清零 inactive locals，拒绝 wrong offset、over-capacity、short/
  trailing tail 和 noncanonical element padding。它不新增 array Ops/IR/main-CFG Emit recipe，
  也不产生 heap collection、pointer 或 persistent allocation。EvmBounded digest
  `44bf1225ed7981aa`、deployment bytecode 828 B；Lean 253、EVM 18 builds、Anvil 18/18。
  Dynamic constructor/return、nested dynamic 与 >64-word frame 继续 fail closed。详见
  `docs/plan/tasks/r1-010.md`。

- R1-011 cross-target codec conformance 已完成：同一 static record、tagged Option 与 bounded
  record-array schema 在 SVM/EVM plan 中保留相同 source projection 顺序；测试同时固定 SVM
  exact/variable Borsh bytes 与 EVM static words/Tagged Tuple/dynamic tail 的差异，避免把它们
  伪装成 shared wire layout。该切片只增加 plan contract，不改产物。详见
  `docs/plan/tasks/r1-011.md`。

- R1-012 shared bounded-vector operations 已完成：`Core.Value.BoundedVec` 提供
  well-formed/capacity/size/empty/full、active-prefix get、checked set/push/pop/clear；固定
  `Vector` 只作 source/extraction frame，不成为 target heap 或持久 pointer。scalar dynamic
  read 在 SVM Borsh locals 与 EVM ABI locals 中分别降为 bounded select；未新增 Core/target
  Ops、Component、CFG 或 Emit case。wide/aggregate element dynamic read 与 mutation writeback
  继续 fail closed。详见 `docs/plan/tasks/r1-012.md`。

- R1-013 bounded Map/Set semantics 已完成：`Core.Collections.BoundedMap` 只用 shared
  fixed-frame `BoundedVec` + `UInt32` active length，提供 bounded lookup、typed reject/replace
  insert、unordered swap-remove、clear 与 no-duplicate validation；`BoundedSet` 复用 unit
  payload。没有 Lean/Std HashMap、Array、allocator、pointer 或 shared physical layout；本片只
  固定 logical laws，SVM account RBMap/allocator 与 EVM hashed storage 的 target binding 继续
  独立排期。详见 `docs/plan/tasks/r1-013.md`。

- R1-014 bounded Queue/BitSet semantics 已完成：`Core.Collections.BoundedQueue` 使用固定
  `Vector` frame + `UInt32` head/length 实现 checked ring FIFO，`BoundedBitSet` 使用编译期
  word count 的 fixed `UInt64` words 实现 packed membership/update。两者都显式拒绝
  malformed/OOB/full case，不分配 heap、不存 pointer、不新增 Ops/IR/Emit，也不声称 shared
  physical persistence；SVM account bytes 与 EVM slots 的 binding 继续独立排期。详见
  `docs/plan/tasks/r1-014.md`。

- R1-015 bounded bytes/string source contract 已完成：`Core.Value.BoundedBytes` 与
  `BoundedString` 使用 type-level capacity + `UInt32` active length + fixed UInt8 frame，byte
  operations 复用 BoundedVec logical laws；strict UTF-8 validator 拒绝 overlong、surrogate、
  truncated 与 >U+10FFFF。两者拥有独立 Codec schema，Profile/Extract 保留 logical identity，
  但本片在 SVM/EVM 明确 fail closed，等待各自 Borsh `Vec<u8>`/`String` 与 ABI `bytes`/`string`
  binding。未新增 Ops/IR/Emit recipe。详见 `docs/plan/tasks/r1-015.md`。

- R1-016 SVM bounded Borsh bytes/String binding 已完成：`Svm.EntryAdapter` 独立拥有
  canonical `u32 length || active bytes`、fixed UInt8 locals、inactive zeroing、capacity/bounds/
  exact-cursor gate；String 在 source 执行前经过 strict UTF-8 wire validator。该变化只扩展
  adapter-owned codec plan interpreter，不新增 Core Ops、SVM Runtime/IR/Component 或 main
  Emit recipe。RawEntry digest `f1e0b094d591bd61`、ELF 21,768 B；Mollusk 17/17；Surfpool
  1.5.0 Loader-v3 22 writes 部署通过。详见 `docs/plan/tasks/r1-016.md`。

- R1-017 EVM bounded ABI bytes/String binding 已完成：`Evm.Codec.DynamicInputPlan` 用 sum type
  统一承载 dynamic tail policy，Packed Bytes v1 独立拥有 standard ABI head offset、32-byte
  length、packed active bytes、zero right-padding、fixed UInt8 locals 与 exact calldata gate；
  String 在 source 执行前验证 strict UTF-8。未新增 Core/EVM Ops、Runtime effect、Component
  或 main CFG Emit recipe。EvmBounded digest `5d657469be1ed0fd`、deployment bytecode 1,421 B；
  solc 0.8.34 与 Anvil 正反矩阵通过。详见 `docs/plan/tasks/r1-017.md`。

- R1-018 SVM bounded Borsh return binding 已完成：独立 `BorshReturnPlan` 把 top-level
  `BoundedVec`、bytes 与 String 的 fixed source frame 编码成 canonical
  `u32 length || active prefix`，不复用 input cursor plan；output String 在发布前独立执行
  strict UTF-8 gate。精确宽度 copy 与 disjoint staging 防止通用表达式 scratch 覆盖动态
  return frame。当前只支持 one-limb scalar element，nested/tagged/wide dynamic return 继续
  fail closed；未新增 Core Ops、SVM Runtime effect、Component 或 collection recipe。RawEntry
  digest `be5151d71eff6bba`、ELF 43,520 B；Mollusk 19/19 与 Surfpool Loader-v3 gate 通过。
  详见 `docs/plan/tasks/r1-018.md`。

- R1-019 EVM bounded dynamic return binding 已完成：独立 `DynamicOutputPlan` 从 fixed source
  frame 发布 canonical standard-ABI `offset || length || active prefix`，不复用 calldata tail
  policy；packed bytes 显式清零 padding，String 在 returndata publication boundary 再做 strict
  UTF-8。output policy identity 进入 EVM IR digest，并包含 array element ABI type 与 capacity。
  当前只支持 one-limb scalar array element，nested/tagged/wide dynamic return 继续 fail closed；
  未新增 Core/EVM Ops、Runtime effect、Component 或 collection recipe。EvmBounded digest
  `dace199d3c7ca718`、deployment bytecode 3,668 B；solc 0.8.34 与 Anvil output 正反矩阵通过。
  详见 `docs/plan/tasks/r1-019.md`。

- R1-020 shared tagged return frame 已完成：Extract 将 direct `Option` 与 payload enum 结果
  投影为固定 `tag + payload lanes` source frame，名称与既有 input-side logical projection
  对齐，但不在 shared 层选择 Borsh/ABI tag width、active-payload 或 wire bytes。首片只开放
  one-limb Option 与 unit/UInt64 enum payload；constructed/richer tagged result 继续 fail closed。
  未新增 Core/target Ops、Runtime effect 或 Emit recipe。详见 `docs/plan/tasks/r1-020.md`。

- R1-021 SVM tagged Borsh return binding 已完成：独立 `BorshReturnPlan` 从 fixed tagged source
  frame 发布 canonical branch-dependent Option/enum bytes，检查 u8 ordinal 与 inactive-zero
  lanes，不复用 input cursor。首片支持 one-limb Option 与 unit/UInt64 enum payload；nested/
  richer/constructed tagged outputs 继续 fail closed。未新增 Runtime/Ops/IR/Component/main Emit
  recipe。RawEntry digest `21207ff5263a4d4a`、ELF 46,336 B，Mollusk 20/20；Surfpool 1.5.0
  以 46 个 Loader-v3 writes 部署核对。详见 `docs/plan/tasks/r1-021.md`。

- R1-022 EVM Tagged Tuple v1 return binding 已完成：统一 `OutputPlan` sum 将 bounded dynamic 与
  tagged tuple 编码收口到 Codec adapter；独立 `TaggedTupleOutputPlan` 从 fixed tagged source
  frame 发布 `(bool,T)` / `(uint8,p0,...)` returndata，并在 output boundary 重新检查 tag、scalar
  range 与 inactive-zero lanes，不复用 calldata plan/locals。首片支持 one-limb Option 与
  unit/UInt64 enum payload；nested/richer/constructed tagged outputs 继续 fail closed。未新增
  Core/EVM Ops、Runtime effect、Component 或 main CFG Emit recipe。EvmCtx digest
  `ded60bb1bab650c8`、deployment bytecode 1,249 B，solc 0.8.34 与 Anvil 5 组 round trip 通过。
  详见 `docs/plan/tasks/r1-022.md`。

- R3-001 persistent SVM SDK foundation 已完成：`Svm.Sdk` 组合 POD Field、fixed Vec/Queue、
  ordered Map/RBMap、one-based allocator 与 canonical initialization；JobQueue/TicketLine 在
  独立 storage account 上复用，持久状态不含 pointer、heap Map/Array 或 invocation scratch。
  详见 `docs/plan/tasks/r3-001.md`。

- R3-002 SVM Account/Signer facade 已完成：`Svm.Sdk.Account.Handle`、`Signer.Handle` 与直接
  alias target plan 的 bounded `Account.View` 把 fixed metadata、required signer 和 runtime
  bounded remaining-account access 收口到 compile-time handles；Trio/AccountView 独立复用。
  extractor 只把既有 account leaves 的 literal gate 扩到 compiler-proven static handle
  projection，不开放 runtime account geometry；全部 SVM 产物逐字节不变。详见
  `docs/plan/tasks/r3-002.md`。

- R3-003 SVM invocation-local transient SDK 已完成：`Svm.Sdk.Transient` 直接复用
  `Heap.State`、`Scratch.Plan` 与既有 invocation-only lifetime，提供 bounded `HeapBuffer`、
  fixed `FixedVec`、`ByteWriter` 和 composed `SignedCpiCodec`。BatchRecorder 与 dynamic signed
  self-CPI 是两个真实 consumer；没有第二套 allocator/plan/lifetime，也没有 persistent
  pointer、heap Map/Array 或新 Ops/IR/Component/main-Emit case。全部 SVM 产物逐字节不变；
  详见 `docs/plan/tasks/r3-003.md`。

- R3-004 SVM static PDA/System facade foundation 已完成：`Svm.Sdk.Pda.Ascii` 封装单个
  compile-time ASCII seed 的 canonical bump/check/signed create，`Svm.Sdk.System` 封装 fixed
  account geometry 的 transfer/createAccount；Pda、Transfer、Create、CreatePda 四个 example
  不再重复 Runtime 名称或 CPI tag/meta/data recipe。Extractor 只新增通用 `pf_inline`→SVM
  Runtime 边界展开，不新增 facade 名字特判；旧单 seed IR 同时补齐 1–32-byte ASCII
  fail-closed gate。四个程序 IR digest 与 12 份 assembly/ELF/IDL 产物保持不变。详见
  `docs/plan/tasks/r3-004.md`。

- R3-005 non-seeded System facade 已完成：`Svm.Sdk.System.assign`、`allocate` 与
  `advanceNonce` 直接组合既有 Runtime wrappers，SysAlloc/Nonce application 不再依赖 Runtime
  名称。账户权限/程序下标仍由 fixed facade geometry 所有，space 是普通 scalar；没有新增
  Ops/IR/Emit/Extract/Component。两个 canonical IR digest 与 6 份 assembly/ELF/IDL 产物保持
  不变；详见 `docs/plan/tasks/r3-005.md`。

- R3-006 classic Token facade 已完成：新增 CPI-relative `CpiAccount.Handle` 与 role-typed
  checked/unchecked transfer descriptors；fixed transfer/mint/burn/account/approve/revoke/freeze/
  authority/native/multisig/data-size wrappers 统一归 `Svm.Sdk.Token`。Phoenix/PhoenixV1Profile
  在 `Examples` 中各自绑定具名 concrete account layouts，业务路径不再重复 positional
  indexes；没有 Phoenix-owned target module，也没有新增 Ops/IR/Emit/Extract/Component。
  42 份相关 assembly/ELF/IDL 产物逐字节不变；详见 `docs/plan/tasks/r3-006.md`。Seeded
  System、general ATA/Memo、Token state/program-id policy 与 Token-2022 extension semantics
  仍是 R3 工作。

- R3-007 fixed ATA/Memo facade 已完成：`Svm.Sdk.AssociatedToken.createIdempotent` 复用现有
  fixed account shape，并明确 external account 5 是 caller-selected Token program，不默认
  classic Token；`Svm.Sdk.Memo.writeOk` 则诚实暴露当前固定 `"ok"` literal。Ata/Memo 应用不再
  依赖 Runtime 名称；没有新增 Ops/IR/Emit/Extract/Component。两个 canonical digest 与六份
  assembly/ELF/IDL 产物保持不变；详见 `docs/plan/tasks/r3-007.md`。普通 ATA Create、
  RecoverNested、program-id policy 与 bounded memo bytes 仍待后续 Runtime/SDK contract。

- R3-008 generic seeded System facade 已完成：`Svm.Sdk.System.AsciiSeed` 提供 compile-time
  ASCII seed 的 allocate/createAccount/assign/transfer，自动编码 bincode seed byte length；
  SysSeed/SysXfer 不再依赖 hardcoded Runtime wrapper。Extractor 只补齐 static literal
  `String.length` → CPI u64 的通用求值，Ops verifier 只在四种 closed System account geometry
  上校验 1–32 ASCII bytes 与长度一致性；没有新 Op/IR/Component/Emit variant 或 recipe。
  `"ledger"` 四路径证明 API 非 `"vault"` 特判，空/超长/错长度均 fail closed；两个 canonical
  digest 与六份 assembly/ELF/IDL 产物逐字节不变。详见
  `docs/plan/tasks/r3-008.md`。Rent-aware resize、general ATA、Token state/program-id policy
  与 Token-2022 extension semantics 仍是 R3 工作。

- R3-009 bounded static Memo facade 已完成：`Svm.Sdk.Memo.Ascii.write` 接收最多 512 bytes
  的 compile-time seven-bit ASCII payload，`writeOk` 只保留为兼容 delegate；Memo 应用显式
  选择 `"ok"`，独立 `"proof-forge"` fixture 证明 API 不是 literal recipe。共享
  `Svm.Memo.Ascii.wellFormed` 同时供 SDK、Extract 与 exact Memo geometry 的 Ops verifier 使用；
  其他 generic CPI `.ascii` words 不受 Memo policy 污染。非 ASCII 与 513-byte payload 在
  emission 前 fail closed；没有动态 String/Vec、persistent pointer、新 Memo opcode 或
  Component/Emit case。Memo assembly/ELF/IDL 逐字节不变；详见
  `docs/plan/tasks/r3-009.md`。Runtime-selected Memo bytes、ordinary/RecoverNested ATA、
  Token state/program-id policy 与 Token-2022 extension semantics 仍是 R3 工作。

- R3-010 general ATA facade 已完成：`CreateAccounts` / `RecoverNestedAccounts` 以具名
  CPI-relative roles 收口官方 Create、CreateIdempotent 与 RecoverNested 的账户权限和
  `[0]/[1]/[2]` discriminant；fixed 与 caller-selected account geometry 都直接组合 generic
  `Runtime.invoke`。旧 `Runtime.ataCreateIdempotent` policy wrapper 已删除，没有新增
  Op/IR/Component/Extract/Emit recipe，也没有动态账户表或持久 pointer。selected Token
  program 可指向 classic Token 或 Token-2022；Ata canonical IR 与 assembly/ELF/IDL 不变；
  详见 `docs/plan/tasks/r3-010.md`。

- R3-011 canonical program-id / SPL Token base-state views 已完成：`Svm.Sdk.Pubkey` 以四个
  little-endian word 表示 compiler-erased 32-byte key，`Svm.Sdk.Program` 提供 System、classic
  Token、Token-2022、ATA 与 Memo v3/v4 的 canonical identity，并组合 executable/full-key/
  owner gate。`Token.AccountState` / `MintState` 以固定 account handles 零拷贝验证 exact
  165/82-byte base layout、state/COption/bool tags，并读取 amount、mint、authority、unaligned
  supply 与 decimals。独立 TokenStateView Mollusk 4/4；PhoenixV1Profile 删除四个本地 Token
  program limbs 后 digest 保持 `af159cb894745102`。没有新增 Runtime/Ops/IR/Component/Emit，
  没有 Array/Map/pointer/heap。详见 `docs/plan/tasks/r3-011.md`。Rent-aware resize、runtime-
  selected/UTF-8 Memo geometry 与 Token-2022 extension semantics 仍是 R3 工作。

- R3-012 source-visible transient Vector64 已完成：`Svm.Sdk.Transient.Vector64` 以编译期
  capacity 绑定 invocation-only `u64` payload，提供 begin/push/set/clear/finish 与 length/get；
  backend 复用与 BatchRecorder 相同的 official-shaped 32 KiB downward bump emitter，full/OOB、
  stale 或 capacity-mismatched handle、OOM 分别返回 `0x1202`/`0x1203`/`0x1201`。`finish`
  只关闭 handle，不伪造 deallocation；pointer 只存在于 target-owned metadata/syscall 邻接
  代码，不进入 source、IR value 或 account state。MemoryOps 与 AccountView 独立消费，且
  effect-preserving Extract 边界逐方法钉死 begin→mutation→query→finish 顺序；没有新增
  top-level Ops/IR/main-Emit recipe。详见 `docs/plan/tasks/r3-012.md`。多个同时 active vector、
  通用元素、pop/insert/remove/iteration 仍是后续 R3 工作。

- R3-013 source-visible transient bounded bytes 已完成：`Svm.Sdk.Transient.Bytes` 以编译期
  byte capacity 绑定同一 32 KiB downward bump allocator，提供 begin/push/set/get/length/
  clear/finish 与固定 `appendLe64`；每个 runtime byte 都验证 `≤255`，完整记录先验容量不足、
  full/OOB、stale/capacity mismatch 与 OOM 均在写入前以独立 terminal code 失败。一个 Bytes
  与一个 Vector64 可同时 active，pointer/metadata 只在 invocation target memory。MemoryOps
  与 AccountView 独立消费；没有 persistent pointer、realloc/free 语义或 top-level Ops/IR/
  main-Emit recipe。下一切片抽取两种 transient emitter 的共同 lifecycle。详见
  `docs/plan/tasks/r3-013.md`。

- R3-014 stable sysvar SDK facade 已完成：`Svm.Sdk.Sysvar.Clock`、`.EpochSchedule` 和 `.Rent`
  把已有 Clock slot/epoch/unix、slots-per-epoch 与 compile-time rent-exemption Runtime contract
  收口为应用侧稳定名称。Clock/Epoch/Rent 三个独立 consumer 保持原 IR digest 和 syscall
  路径；本切片没有新增 syscall、Runtime leaf、Ops/IR/Component/Emit、scratch 或持久状态。
  详见 `docs/plan/tasks/r3-014.md`。generic sliced sysvar、Instructions sysvar、stack height、
  remaining compute 与其余 Clock/Epoch 字段仍属 R2/R3 Runtime backlog。

- R3-015 shared transient lifecycle emitter 已完成：`Svm.Transient.Emit.Lifecycle` 统一
  Vector64/Bytes 的 official-shaped bump allocation、pointer/length/capacity/active metadata、
  active/capacity gate、clear 与 non-reclaiming finish；两个具体 emitter 只保留 u64/byte
  element 操作与各自错误。source API、IR digest、assembly byte count 和 Mollusk 行为不变，
  没有新增 top-level Ops/IR/CFG/main-Emit recipe 或 pointer-valued source/state。详见
  `docs/plan/tasks/r3-015.md`。下一切片可在该 lifecycle 上增加同类型多 handle 或 generic
  POD/record writer，而不再复制 allocator/metadata assembly。

- R3-016 bounded transient log-data binding 已完成：`Transient.Bytes.logData` 把 active prefix
  作为一个官方 `sol_log_data` field 发布；`SolBytes` descriptor 只在 syscall 邻接的 16-byte
  target scratch 中按 `[addr,len]` 构造，payload 不复制，source/IR/account state 不出现 pointer。
  active/capacity gate 继续复用 shared lifecycle；MemoryOps 的真实 Mollusk 路径同时钉死 exact
  base64 payload 与普通 u64 return data。没有新增 top-level Ops/IR/main-Emit recipe，也不声称
  已覆盖多 field、字符串、pubkey、numeric log 或 return-data API。详见
  `docs/plan/tasks/r3-016.md`。

- R3-017 transient Vector64 pop 已完成：`Transient.Vector64.pop` 在既有 active/capacity gate
  后拒绝 empty (`0x1202`)，原位把 logical length 减一并返回旧尾元素。它不分配、不清 payload、
  不 reclaim/realloc，也不让 pointer 离开 target-owned emitter；Runtime leaf 只由既有 generic
  Component bridge 解码。MemoryOps Mollusk 钉死 LIFO 与 empty failure，产物 digest
  `e37f469f33e44884`、ELF 41,440 B。没有增加 top-level Ops/IR/main-Emit recipe。详见
  `docs/plan/tasks/r3-017.md`。

- R5-001 EVM Access foundation 已完成：`Evm.Sdk.Access` 组合 existing Address/Context/Revert
  提供 owner/running gates 和 fixed single-pending two-step ownership。TwoStepCounter/Credits
  独立复用；replacement 会使旧 nominee 失效，accept/cancel 显式清零，不使用 hashed
  nomination map、隐藏 write、magic slot 或 policy Emit case。Extractor 同时修复 direct
  one-field State store 与 wide-leaf path 误判；详见 `docs/plan/tasks/r5-001.md`。

- R5-002 EVM static storage declaration foundation 已完成：`Evm.Sdk.Storage.Static` 在抽取期
  分配 scalar、Address/wide、flat record、fixed array/record-array typed handles；声明表与
  两个独立 contract 的真实 State flattening 逐槽对照，Anvil 直接验证 constructor 和
  targeted mutation。它不改变 hashed-map base，不增加 runtime allocator、隐藏 storage
  write 或 Component/Emit recipe；详见 `docs/plan/tasks/r5-002.md`。

- R5-003 EVM bounded static roles 已完成：`Evm.Sdk.Roles.Set2` 对两个显式 Address slot
  提供 membership/grant/revoke 纯决策；EvmStaticCounter/EvmStaticRoster 分别以 operator/writer
  角色独立复用。权限与错误策略留在 application，所有写入仍是 literal State field update；
  不使用 Vector、hashed role map、runtime slot allocator、隐藏 write 或新 Ops/IR/Emit case。
  Anvil 覆盖 zero/duplicate/full/nonmember/unauthorized/closed policy；indexed Address return
  在 extraction 支持安全 OOB-zero 前不发布。详见 `docs/plan/tasks/r5-003.md`。Reentrancy 已由
  R5-009 完成；asset/NFT components 仍未完成。

- R5-004 EVM Pausable policy 已完成：`Evm.Sdk.Pausable` 统一 canonical `UInt8` flags、
  fail-closed predicates、replacement transitions 与现有 `Paused()` terminal；
  TwoStepCounter/Credits 直接复用，权限、事件和 literal State writes 仍归 application。
  Extract 只把 `pf_inline` scalar helper 的通用合同补齐到 UInt8/16/32，没有 Pausable 名字、
  新 Ops/IR/Component/Emit case 或隐藏 slot。两个 contract 的 Yul/ABI/bin 逐字节不变；详见
  `docs/plan/tasks/r5-004.md`。Typed pause events 仍等待 generic event surface；R5-009 已在
  独立 ordered storage effect 上证明 ReentrancyGuard 的 lock → CALL → clear ordering。

- R5-005 EVM bounded payment facade adoption 已完成：`Evm.Sdk.Payments` 独立拥有 Ether、
  ERC-20、WETH 与 fixed-path Uniswap V2 的 contract-facing 名称，仍复用既有 closed Runtime、
  CallResult 和 payable contracts；Vault/TipJar/Ownable 改为只 import `Evm.Sdk`，不再直连
  Runtime/ClosedCall/NativeFx/HashedMap source boundary。三个 canonical IR digest 与九份
  Yul/ABI/bin 产物逐字节不变；没有新增 selector、Ops/IR/Component/Emit case 或任意 calldata。
  详见 `docs/plan/tasks/r5-005.md`。Code-existence、revert bubbling 与 arbitrary call 仍 fail
  closed；reentrancy 保护只在 consumer 显式组合 R5-009 时成立。

- R5-006 EVM fungible debit ledger foundation 已完成：`Evm.Sdk.Fungible.Balances` 在显式
  `AddressMap256` handle 上统一 balanceOf/canDebit/debit/insufficient；Token 的 burn/burnFrom
  与 Credits 的 claim 两种独立 policy 复用同一 O(1) persistent ledger component。权限、pause、
  zero-address、supply/cap、allowance 与 event sequencing 仍在 application；没有新
  Runtime/Op/IR/Component/Emit case、slot allocator 或 selector/topic recipe。两个 source
  digest 与六份 Yul/ABI/bin 产物逐字节不变；详见 `docs/plan/tasks/r5-006.md`。Credit/mint、
  same-address-safe transfer、allowance core、ERC-721 与 bounded ERC-1155 仍是 R5 工作。

- R5-007 EVM checked credit/alias-safe transfer 已完成：`Fungible.Balances` 新增
  canCredit/credit/canTransfer/transfer，credit 以 `next ≥ current` 拒绝 UInt256 wrap，transfer
  在 source/destination 相同时通过 debit gate 后不写同一个 hashed key 两次。Token mint 改为
  additive balance credit，并以 `value ≤ cap - supply` 阻断 supply wrap；direct/delegated
  self-transfer 保持 balance，其中 delegated path 仍消费 allowance。Vault share ledger 是第二个
  additive credit consumer。权限、pause、zero-address、allowance 与 event ordering 仍显式留在
  application；没有新 Runtime/Op/IR/Component/Emit case。Token/Vault ABI 不变，Anvil 覆盖重复
  mint/credit、wraparound rejection、direct/delegated self-transfer 与失败原子性；详见
  `docs/plan/tasks/r5-007.md`。Reusable allowance core、ERC-721 与 bounded ERC-1155 仍是 R5 工作。

- R5-008 EVM checked allowance core 已完成：`Fungible.Allowances` 在显式
  `AddressPairMap256` handle 上统一 allowanceOf/approve、checked increase/decrease/spend 与
  Insufficient terminal。increase 用 `next ≥ current` 拒绝 UInt256 wrap，decrease/spend 在写前
  要求 current ≥ amount。Token 与 Ownable 独立复用；Token 仍显式拥有 pause/zero-address、
  permit、授权和 Approval/Transfer ordering，Ownable 工程 fixture 从 UInt64 overwrite 改为
  UInt256 checked subtraction。没有新 Runtime/Op/IR/Component/Emit case 或 allowance recipe。
  Token ABI 不变，Ownable ABI 的 uint64→uint256 是有意的 ledger contract 修正；Anvil 覆盖
  allowance wrap、over-spend 与失败原子性。详见 `docs/plan/tasks/r5-008.md`。ERC-721 与
  bounded ERC-1155 仍是 R5 工作。

- R5-009 EVM reusable reentrancy policy 已完成：`Evm.Sdk.Reentrancy` 在显式
  `Storage.Static.Handle UInt64` 上统一 OpenZeppelin-compatible `1/2` sentinels、fail-closed
  entry gate 与 ordered enter/leave。GuardedPayout/EvmOrderedStorage 两个 consumer 都抽取为
  `store 2 → CALL → store 1`，没有隐藏 final write 或新 Runtime/Ops/IR/Component/Emit case。
  hostile Solidity callback 在 Anvil 观察到 entered=2，nested payout 原子拒绝；normal CALL、
  outer restore 与 failed-CALL rollback 均通过。详见 `docs/plan/tasks/r5-009.md`。

- R5-010 EVM persistent bounded storage vector 已完成：`Evm.Sdk.StorageVec` 以普通 static
  State 字段（`Vector UInt64 capacity` backing + 相邻显式 length scalar）绑定共享
  `Core.Value.BoundedVec` active-prefix 语义。SDK 拥有纯决策（wellFormed/canPush/canPop/
  canGet/canSet/canClear，full/OOB/malformed fail closed），consumer 保持每个物理 field write
  显式；没有 runtime slot allocator、host pointer、新 Ops/IR/Emit recipe 或无界循环。
  EvmVecLog（owner-gated log，capacity 4）与 EvmVecStack（permissionless LIFO，capacity 3）
  独立复用；worst-case slot/gas shape 为 O(1) 且与 capacity 无关，stale-slot 与注入的
  malformed-length 原子失败由 Anvil 直接核对。详见 `docs/plan/tasks/r5-010.md`。

- R2-002 SVM bounded scratch/instruction layout 已完成：`Svm.Scratch` 用 typed region handles
  统一 static invoke 与 dynamic signed self-CPI 的 metas/descriptor/data/infos/signer-tail
  geometry；malformed bank、重复 region、非法 alignment 与 1,024-byte OOM 均在 emission 前
  fail closed。plan 只含编译期 byte counts，不持有或持久化 native pointer；没有新增
  Ops/IR/Component/Emit recipe。全部 registered SVM program 的重构前后 assembly
  逐字节一致；详见 `docs/plan/tasks/r2-002.md`。

- R2-003 SVM signer-tail/return-data staging 已完成：ordinary invoke 与 dynamic signed
  self-CPI 的 copied seed bytes、aligned bump、seed descriptors 和 signer group 统一由
  `SignerSeedTail` 规划；`sol_get_return_data` 的固定 32-byte program id + 8-byte payload 由
  `ReturnDataStaging` 规划。全部 region 经 `Plan.alloc` 做 alignment/capacity gate，不携带或
  持久化 pointer；已有 assembly 逐字节不变。详见 `docs/plan/tasks/r2-003.md`。

- R2-004 SVM Token-2022 TLV envelope 已完成：target-owned plan/reference cursor 按 pinned
  SPL Token-2022 layout 验证 base、mint padding、AccountType、little-endian TLV header 与
  `data_len`；cursor state 只有 UInt64 offset/count/duplicate bitmap，generated sBPF 不含
  Array/List/Map 或 persistent pointer。当前 closed specialization 接受 classic base 与
  official end/padding form，transfer-fee、hook、unknown/malformed 继续在 CPI 前原子拒绝；
  53 个不相关 SVM 产物逐字节不变。详见 `docs/plan/tasks/r2-004.md`。

- R2-005 SVM checked program-memory spans 已完成：`Svm.Sdk.Memory` 用编译期固定
  account/offset/length descriptor 暴露 memcpy/memmove/memcmp/memset；component backend 在
  syscall 前检查 actual data length，写目标另查 writable 和 current-program ownership。
  memcpy 静态拒绝 overlap，memmove 保留 overlap，memcmp 返回 exact i32 bits；source/IR/account
  state 均不出现 pointer 或 heap collection。MemoryOps 覆盖四个 host contracts，AccountView
  独立复用 compare。详见 `docs/plan/tasks/r2-005.md`。

- R2-006 SVM invocation telemetry 已完成：`Svm.Sdk.Telemetry` 提供 remaining compute、
  stack height、compute diagnostic 与 fixed five-word hexadecimal logger；target-owned
  `Svm.Telemetry` 经 generic Component bridge 绑定四个 exact official syscall symbols，不新增
  top-level Ops/IR/main-Emit recipe。所有参数/结果都是 scalar UInt64，没有 Array/String/Vec、
  allocation 或 pointer；Mollusk 验证 top-level height=1、live compute snapshot 与两个 logger。
  Info digest 为 `92992971c8b3fd12`、ELF 为 8,536 B；Surfpool 1.5.0 以九个 Loader-v3
  writes 部署并核对 complete ProgramData bytes。详见 `docs/plan/tasks/r2-006.md`。

- R4-001 EVM typed call-result contract 已完成：`Evm.CallResult` 用一个 interpreter 统一
  closed CALL/STATICCALL 的 success-only、exact-word 与 ERC-20 empty-or-nonzero-word policy，
  最多复制 32 bytes returndata。`ClosedCall.Emit` 的既有 consumers 全部迁移且
  Vault/Token artifacts byte-identical；没有开放 arbitrary call、delegatecall/create 或隐藏
  allocation。详见 `docs/plan/tasks/r4-001.md`。

- R4-002 EVM typed LOG/custom-error plan 已完成：`Evm.LogError` 统一 LOG0..4 topic/data
  geometry 与 ABI custom-error selector/argument/revert-length geometry；NativeFx 和 permit
  继续拥有 closed event/error 语义，只把 materialized words 交给唯一 interpreter。全部 20 个
  EVM Yul/bin/ABI 产物逐字节不变，没有开放 arbitrary opcode/signature/selector。详见
  `docs/plan/tasks/r4-002.md`。

- R4-003 EVM payable/receive policy 已完成：`Evm.Payable` 以 typed value gate 和 calldata
  route 统一 constructor/runtime/selector nonpayable rejection、deposit exact CALLVALUE、
  receive accept-any binding、empty-calldata receive 与 selector dispatch；唯一 interpreter
  对 impossible gate/route/operand shape fail closed。source API、IR/digest、ABI payable labels
  与全部 20 个 EVM 产物逐字节不变；native send CALL 继续归 closed NativeFx/CallResult
  policy。详见 `docs/plan/tasks/r4-003.md`。

- R4-004 EVM closed ecrecover contract 已完成：`Evm.Precompile` 固定 address `0x01`、
  128-byte `hash | v | r | s` frame、32-byte output，以及 STATICCALL success、exact
  returndata、nonzero signer 三道门；`ClosedCall.Emit` permit 消费唯一 interpreter。exact-size
  门拒绝 invalid ecrecover 成功但返回空数据时读取 stale output memory；其余 precompile、
  arbitrary STATICCALL/delegatecall/create 仍不开放。只有 Token Yul/bin 因新增门发生预期变化，
  全部 ABI 与 IR digests 不变。详见 `docs/plan/tasks/r4-004.md`。

- R4-005 EVM ordered static UInt64 store 已完成：`Evm.StaticStorage` 通过既有 Component
  bridge 保留 `store → CALL → store` lexical order，`Storage.Static.Handle.storeNow` 只接受
  compiler-static typed handle，emitter 再对真实 program schema 校验 field 与 8-byte width；
  source 不接触 slot 魔数。该 effect 与普通 final State writeback 分离，失败 CALL 由 EVM
  transaction rollback entered write。focused extraction、solc 和 Anvil 均通过；详见
  `docs/plan/tasks/r4-005.md`。R5-009 已组合此 effect 为 reusable Reentrancy policy。

- R4-006 EVM full-width environment 已完成：`Runtime` / `Sdk.Context` 提供 allocation-free
  `UInt256` gasleft/basefee/prevrandao/gaslimit；wide environment renderer 每个结果只读一次
  opcode 并复用四 limb 投影。solc 0.8.34 assembly 显式固定 Cancun，避免 `0x44` 的旧
  DIFFICULTY 语义；`callerLow`/`selfLow` 截断投影也由 `Sdk.Context` 显式拥有，EvmCtx 和
  TipJar 均不再直接 import Runtime，Anvil 与当前 block 字段精确对照。详见
  `docs/plan/tasks/r4-006.md`。

- R4-007 EVM source custom-error ABI metadata 已完成：ABI emitter 从完整 structured op tree
  自动收集 `.errorNamed`，覆盖 `ite` 与 bounded `forBody`、按首次出现顺序去重，并输出与
  既有 Yul selector-only revert 完全一致的 zero-argument error 项。新增 error enum 不再需要
  修改硬编码 ABI 列表；EvmVecLog/Stack 的 malformed/oob/empty 已进入真实 artifact。该切片
  不新增 Ops/IR/Runtime recipe，不改变 Yul、bytecode 或 digest。详见
  `docs/plan/tasks/r4-007.md`。

- R4-008 EVM environment component boundary 已完成：production gasleft/basefee/prevrandao/
  gaslimit source extraction 现在只生成 generic Component query，由一个 target-owned
  interpreter 做单次 full-width observation 和四 limb 投影；legacy Golden constructor 暂留
  compatibility，但后续 environment 能力不再扩 top-level Ops/IR/main Emit。EvmCtx/TipJar 的
  digest、Yul、ABI、bytecode 均逐字节不变。详见 `docs/plan/tasks/r4-008.md`。

- R4-009 EVM coinbase/blockhash environment slice 已完成：`Sdk.Context` 新增完整 20-byte
  `coinbase : Address` 与 `blockHash (UInt64) : UInt256`，production extraction 仍只生成
  generic Component query。target-owned Environment interpreter 对每个结果只执行一次
  COINBASE/BLOCKHASH 并复用三/四 limb 投影，没有新增 top-level Ops/IR/main Emit recipe、
  allocation、storage 或 call。EvmCtx digest `14d95bb9d9e56f95`、bytecode 1,447 B；TipJar
  digest `3387209f8b9b4b1f`、bytecode 2,480 B；focused Anvil 与真实 block beneficiary/hash
  精确一致。详见 `docs/plan/tasks/r4-009.md`。

- R4-010 EVM address code observations 已完成：`Sdk.Address` 新增 `codeSize : UInt64` 与
  `codeHash : Bytes32`，完整三-limb Address 通过已有 fixed 32-byte packing helper 绑定
  EXTCODESIZE/EXTCODEHASH；hash 只执行一次 opcode，并按 source-order FixedBytes 投影四
  limb。production extraction 仍只生成 Environment Component query，没有 top-level
  Ops/IR/main Emit recipe、allocation、storage 或 call。EvmCtx digest
  `937893f551c87688`、bytecode 2,415 B；Anvil 核对 deployed self code size/hash 以及
  nonexistent account 的 size=0/hash=0。详见 `docs/plan/tasks/r4-010.md`。

- E-U256-004 checked division/modulo 已完成：typed `Division` query 通过既有 `WideWord`
  component 固定打包两个四-limb word，由 target interpreter 在 `div`/`mod` 前统一拒绝零
  divisor；SDK 不暴露 raw EVM 零除返回 0 的语义。该纯值路径不分配 heap/memory buffer、
  不写 storage、也不新增 main Emit recipe。详见 `docs/plan/tasks/e-u256-004.md`。

- `lake build Tests` 当前 326 jobs，汇总门覆盖全部 imported test modules 与 target guards。
- SVM registry 56 个程序；这表示每个程序有门，不表示每个入口都已有链上矩阵。全量
  `pf build` 当前通过；全套 Mollusk 322/322，其中 RawEntry 20/20、Phoenix-v1 profile
  76/76。
- EVM registry 20 个程序；Counter / Pair / Flag / Maybe / Context / EvmBounded /
  EvmStaticCounter / EvmStaticRoster / TipJar / Lang / Vault / Ownable / Token / Capped /
  TwoStepCounter / Credits / Window / Phase / Wide / Const 均进入
  Anvil 总门。`Addr20` 是一等 ABI `address`；
  显式 `UInt256` 使用 checked add/sub/mul、typed unsigned eq/lt/le/gt/ge 和 ABI `uint256`，
  以及 typed bitwise AND/OR/XOR/complement/logical shift 和 checked div/mod；默认算术仍是
  `UInt64`。这些操作全部复用 `WideWord` component，不增加 main Emit recipe。详见
  `docs/plan/tasks/e-u256-002.md`、`docs/plan/tasks/e-u256-003.md`、
  `docs/plan/tasks/e-u256-004.md`。
  地址的 little-endian limbs → ABI word 转换由 runtime `pf_store_addr20` helper 统一实现，不再
  在每个 CFG case 展开二十条 `mstore8`；solc 0.8.34 strict Yul optimizer 可编译完整 Token，
  全 20 个 build 与 Anvil 20/20 通过。详见 `docs/plan/tasks/evm-009.md`、
  `docs/plan/tasks/r1-010.md`、`docs/plan/tasks/r5-001.md` 和 `docs/plan/tasks/r5-002.md`。
- Phoenix Mollusk 8/8：ask/bid 挂单、reduce、双向撮合、费用收取、真实 base/quote deposit/withdraw、trader topology 删除后的 surviving root、ask/bid order topology 与满书 exact address reuse、未注册 take-only 双 Token 腿、严格 slot/time TIF、三种 self-trade、认证 audit `Program data`，及 vault/mint/Token program/self program/log PDA/writable/signer/owner 原子失败；跨四档逐样本 refinement 仍由 host/IR 门承担。
- `postAskFunds → detached → insertAskOrder` 的 aggregate `baseLocked` / `baseFree` stores 已恢复：`flattenLeaves` 先 reduce constructor projection，再给闭包了 bounded tree walk 的 scalar 字段足够 decoder fuel。IR 门钉住 `postAsk` 的 `baseLocked`/`baseFree` 和 `postBid` 的 `quoteLocked`/`quoteFree`。
- P4 通用压缩 / Loader-v3 部署资格：Core `shareBlocks` 从相邻比较升级为全图 fingerprint 分桶 + 精确结构相等，已知 redirect 先归一化；collision 不会错误共享。Phoenix CFG 6,128 → 5,151 blocks；实测 `pf build --target svm Phoenix`：digest `7a969da7b60ead4`，assembly 10,642,331 bytes，ELF 3,429,336 bytes，IDL 19,626 bytes，比上一 checkpoint 再减 244,637 / 75,440 bytes。Assembler 按 Agave 4.0 Loader-v3 `ProgramData` 10 MiB、metadata 45 B，强制 ELF ≤ 10,485,715 B；当前 headroom 7,056,379 B。Surfpool 1.5.0 offline smoke 禁用 instant direct-state 路径，以 3,389 个 Loader write transactions + deploy + authority transfer 完成本地部署；confirmed signature、Program/ProgramData layout 与完整 ELF bytes 全部核对。本轮 `lake build Tests`、全 49 个 SVM `pf build`、Mollusk 198/198（含 Phoenix 8/8 与 Tree 2/2）及 Anvil 12/12 全绿；不作公网部署声明。
- P5 第一段 profile gate 已完成：通用 `accDataWord acc word` 对编译期固定账户/word 做 `data_len` 边界检查；独立 `PhoenixV1Profile` verifier 验证官方 program owner、MarketHeader discriminant、12 个官方 `(bids, asks, seats)` tuple 与 exact account length，最小 profile 返回 84,944 B。它不读取 market body，也不宣称完整 Phoenix-v1 兼容。产物 ELF 26,064 B；12 个 tuple 全部进入 profile Mollusk 3/3，全量 Mollusk 201/201 与 Anvil 12/12 通过。
- P5 第二段静态 body metadata gate 已完成：官方 Sokoban tree 是账户内固定 `[Node; N]` 与 bump/free-list allocator，不是 Rust heap Map。本切片只按四档 compiled profile 读取固定 sequence、bids/asks/traders allocator `size` word，并检查 count ≤ capacity；不开放 runtime offset、节点遍历/写入或 remaining accounts。`PhoenixV1Profile` digest `39d77b7c712ba581`，ELF 80,576 B；12 个 profile 的 scalar/count 与三类超限失败进入同一 Mollusk 3/3。
- P5 第三段 allocator header envelope 已完成：按四档固定 word 验证三棵树的 root/padding、1-based bump/free-list cursor、size/root/capacity 关系；checkpoint digest `3322a44e27b16f42`，ELF 156,200 B。
- P5 第四段 bounded root slot 已完成：通用 `accDataWordAt` 只允许运行时 slot，account/base/stride/capacity 均编译期固定，并做 slot + 最终 data-length 双边界。bid root index=2 的 links/parent/color/price 直接从账户读取；无 heap/Map/节点复制。当前 digest `b2519600b8cfe99f`，assembly 878,132 B，ELF 282,536 B；profile Mollusk 4/4。
- P5 第五段 constant-memory root neighborhood 已完成：四档 profile 原位读取 bid root 与两个直接 child，验证 bid side tag、child→parent reciprocity、color、index envelope 及局部 price/sequence ordering；不分配节点容器，也不声明全树验证。当前 digest `7952977f008911a8`，assembly 2,171,011 B，ELF 716,344 B；profile Mollusk 4/4。
- P5 第六段本地部署门已完成：Surfpool smoke 参数化为 Phoenix / PhoenixV1Profile 两个显式目标；P5 verifier 的 716,344 B ELF 经 708 个 Loader write + deploy + authority transactions 落入 exact 716,389-byte ProgramData，confirmed signature 与完整 bytes 已核对。默认 Phoenix 3,389-write 路径也重跑通过；不用 `solana-test-validator`，不声明公网部署。
- P5 第七段 bounded parent path 已完成：通用 `accDataParentPathValid` 以静态
  base/stride/capacity/max-depth 逐步读取账户内 parent path，验证 color、index envelope、
  parent→child reciprocity，并在 32 edge 内要求到 root；root 外 reciprocal cycle 有界返回 0。
  当前 digest `381c728318e7fe26`，assembly 2,509,900 B，ELF 821,576 B；无 heap/Map；
  Surfpool 1.5.0 以 812 个 Loader write transactions 部署并核对 exact ProgramData。
- P5 第八段 whole bid tree + allocator partition 已完成：通用 `accDataRbTreeValid` 以
  iterative parent-pointer traversal 和固定 4096-bit stack bitmap 原位验证 root/color、
  reciprocity、red rule、equal black height、strict Phoenix FIFO ordering、reachable live count，
  再验证 free-list 无 cycle/duplicate/live overlap 且精确覆盖全部 pre-bump slot；无 heap、
  Map、node copy 或 persistent pointer。4095-node / 4096-capacity perfect tree 在 Mollusk 中
  消耗 852,066 CU。当前 digest `53d37673dbf95305`，assembly 2,876,110 B，ELF 936,264 B；
  Surfpool 1.5.0 以 926 个 Loader write transactions 部署并核对 exact 936,309-byte
  ProgramData。
- P5 第九段 whole ask tree 已完成：四档 ask allocator 复用同一 fixed-memory validator，
  额外强制 ask side tag=0 与 `(price, stored sequence)` strict ascending FIFO；4095-node /
  4096-capacity perfect ask tree 消耗 852,060 CU。当前 digest `1356885e6582aab2`，assembly
  3,242,689 B，ELF 1,050,952 B；Surfpool 1.5.0 以 1,039 个 Loader write transactions
  部署并核对 exact 1,050,997-byte ProgramData。
- P5 第十段 whole registered-trader tree 已完成：十二个官方 profile 选择固定
  base/18-word stride/capacity，通用 `accDataRbTreeKey4Valid` 直接扫描账户内节点，以固定
  8321-bit bitmap + 64-entry stack 验证完整 RB invariants、child-parent reciprocity、
  Rust `[u8;32]` byte-lexicographic Pubkey strict ordering 和 exact live/free partition；不复制
  node，不使用 heap/Map 或持久 pointer。最大 8321-capacity allocator 的 8191 live + 130
  free slots 消耗 1,344,959 / 1,400,000 CU。当前 digest `6d8e6cbb2d5dd163`，assembly
  3,703,126 B，ELF 1,194,760 B；Surfpool 1.5.0 以 1,181 个 Loader write transactions
  部署并核对 exact 1,194,805-byte ProgramData。
- P5 第十一段 bounded account-resident write 基础已完成：通用 `accDataWordSetAt` 把
  account/base/stride/capacity 固定在编译期，只让运行时选择 slot 和 u64 value；只写外部
  writable、current-program-owned account，并在 store 前检查 account count、capacity 和
  最终 data length。它是有序 target effect / CFG CSE barrier，不返回或持久化 pointer。
  `writeTraderTopology128` 连续原位写最小 profile 的 links 与 parent/color；readonly、错误
  owner、slot 128 和“第一字可写、第二字越界”的短账户均 `Custom(1)` 且原子回滚。
  当前 digest `f77c4fc2ca622dc9`，assembly 3,709,362 B，ELF 1,196,400 B，IDL 3,386 B；
  Surfpool 1.5.0 以 1,183 个 Loader write transactions 完成本地部署并核对 exact
  1,196,445-byte ProgramData。本轮 194-job Lean、50 个 SVM build、Mollusk 210/210 和
  Anvil 12/12 全绿。
- P5 第十二段 exact first trader registration 已完成：按 Sokoban 0.3.0 的真实
  16-byte registers + 32-byte Pubkey + 96-byte TraderState 节点布局，把 canonical fresh
  128-seat allocator 从 root/size=0、bump/free=1 原子变成 slot 1 黑根、root/size=1、
  bump/free=2。完整 144-byte slot 均覆盖，guarded `Except` 分支内 21 个 ignored effects
  不再被最终 state projection 吞掉；成功后 complete trader validator 返回 1，不暴露
  detached node。nonempty/profile 错误、readonly 和 wrong owner 均原子失败。当前 digest
  `e6a7a4e2393cc64f`，assembly 3,759,660 B，ELF 1,209,400 B，IDL 3,721 B；Surfpool 1.5.0
  以 1,196 个 Loader write transactions 部署并核对 exact 1,209,445-byte ProgramData。
- P5 第十三段 exact second trader registration 已完成：canonical one-root 128-seat tree
  经 bump path 分配 address 2，完整覆盖第二个 144-byte slot，以 parent=1/color=Red 挂到
  黑根 left 或 right，不发生 rotation。四个 little-endian limb 各自 byte-swap 后逐 limb
  比较，精确复现 Rust `[u8;32]` Pubkey ordering；测试 key 刻意让该顺序与 u64 数值序相反。
  duplicate/malformed、readonly/wrong owner 均原子失败，左右结果都通过 complete tree/
  allocator validator。当前 digest `f741f2eaffde779e`，assembly 3,888,574 B，ELF
  1,248,584 B，IDL 4,058 B；Surfpool 1.5.0 以 1,234 个 Loader write transactions
  部署并核对 exact 1,248,629-byte ProgramData。本轮 194-job Lean、50 个 SVM build、
  Mollusk 212/212 和 Anvil 12/12 全绿。
- P5 第十四段 exact third trader registration 已完成：canonical two-node 128-seat tree 经
  bump path 分配 address 3，完整覆盖第三个 144-byte slot，并按 Sokoban 0.3.0 精确产生
  LL/LR/RR/RL rotation/recolor 与两个 no-fix topology。通用 `svmByteSwap64` 在宿主侧保持
  纯语义，SVM 侧直接发射 `be64`，不引入 heap allocation；external-account write 只要出现
  但任一 operand 无法解码，抽取就 fail closed，不再静默丢 effect。六种结果逐字节匹配并
  通过 complete trader tree/allocator validator；duplicate/malformed/readonly/wrong owner
  均原子失败。当前 digest `d9b9ee673526ff9f`，assembly 3,949,948 B，ELF 1,261,744 B，
  IDL 4,392 B；Surfpool 1.5.0 以 1,247 个 Loader write transactions 部署并核对 exact
  1,261,789-byte ProgramData。本轮 194-job Lean、50 个 SVM build、Mollusk 214/214 和
  Anvil 12/12 全绿。
- P5 第十五段 exact fourth trader registration 已完成：任意 canonical three-node trader
  tree 必为 black root + two red leaves；本切片从六种 address assignments bump-alloc
  address 4，覆盖四个 key intervals，把新节点挂到 selected red parent，并按 Sokoban
  red-uncle path 把两个 existing leaves recolor black，root 地址不变。slot 4 的 18 words
  全部覆盖，三个既有 TraderState 逐字节保留，成功路径精确 23 个 account writes；三种
  duplicate、malformed、readonly/wrong owner 均原子失败。fixed-memory tree/parent-path
  intrinsic 现在保存 walked ABI 的 `r7` instruction-data base，traversal 不再破坏后续参数
  读取。当前 digest `a2c228178be89985`，assembly 4,078,543 B，ELF 1,300,352 B，
  IDL 4,727 B；Surfpool 1.5.0 以 1,285 个 Loader write transactions 部署并核对 exact
  1,300,397-byte ProgramData。本轮 194-job Lean、50 个 SVM build、Mollusk 216/216 和
  Anvil 12/12 全绿。
- P5 第十六段 exact fifth trader registration 已完成：canonical four-node tree 经 bump
  path 分配 address 5，完整覆盖第五个 144-byte slot。若 parent 为 black，只填 missing
  child；若 parent 是唯一 red address-4 leaf，则按 Sokoban black/null-uncle 路径执行
  LL/LR/RL/RR local rotation/recolor，并保持最上层 black root 地址不变。八种逐字节结果
  覆盖全部六种既有 address layout、四种 rotation 和两侧 black-parent insertion；四个
  existing TraderState 保留，结果都通过 complete tree/allocator validator。四个
  duplicate、malformed、readonly/wrong owner 均原子失败。持久状态仍只使用 one-based
  slot index 与 `0` sentinel，不引入 heap/Map、节点副本或 persistent pointer。当前 digest
  `9140326aef66cbdc`，assembly 4,378,054 B，ELF 1,399,096 B，IDL 5,061 B；Surfpool 1.5.0
  以 1,383 个 Loader write transactions 部署并核对 exact 1,399,141-byte ProgramData。
  本轮 194-job Lean、50 个 SVM build、Mollusk 218/218 和 Anvil 12/12 全绿。
- P5 第十七段 general bounded trader insertion 已完成：通用
  `accDataRbTreeKey4Insert` 以编译期固定 geometry 在账户原位执行 bounded search、
  bump/free-list allocation 与完整 RB insert fixup，不再继续增加第六/第七次特例。
  `lib-sokoban = 0.3.0` differential test 用 128-key permutation 填满全部 seat，并在每次
  插入后精确比较完整 18,464 bytes；官方 delete 产生的 free head 也能逐字节复用。
  duplicate/full/malformed/readonly/wrong owner 全部在 store 前原子失败。IDL 现在从
  instruction effect 推导 external writable meta。持久状态仍只有 one-based index 与
  `0` sentinel，不使用 heap/Map 或 persistent pointer。当前 digest `ea2110304454c9e6`，
  assembly 4,413,033 B，ELF 1,410,648 B，IDL 5,499 B；Surfpool 1.5.0 以 1,394 个
  Loader write transactions 部署并核对 exact 1,410,693-byte ProgramData。本轮
  194-job Lean、50 个 SVM build、Mollusk 220/220 和 Anvil 12/12 全绿。
- P5 第十八段 general bounded trader removal 已完成：通用
  `accDataRbTreeKey4Remove` 在完整 tree/free-list preflight 与 key lookup 后，按 Sokoban
  0.3.0 原位执行 predecessor transplant、bounded delete-fixup 和 free-list push。128-key
  tree 以独立 permutation 逐个删空，每一步完整 18,464 bytes 与官方实现一致；随后 16 次
  insertion 也精确复用同一 LIFO free-list。持久状态仍只有 one-based index / `0` sentinel，
  不使用 heap/Map、detached node 或 persistent pointer。当前 digest `74f755a74720a766`，
  assembly 4,456,725 B，ELF 1,424,912 B，IDL 5,842 B；Surfpool 1.5.0 以 1,409 个 Loader
  write transactions 部署并核对 exact 1,424,957-byte ProgramData。本轮 194-job Lean、
  50 个 SVM build、Mollusk 222/222 和 Anvil 12/12 全绿。
- P5 第十九段 fixed-capacity bid/ask insertion 已完成：通用
  `accDataRbTreeOrderInsert` 以官方连续 8-word / 64-byte order slot 原位保存 2-word
  `FIFOOrderId` 与 4-word `FIFORestingOrder`，按 bid descending / ask ascending comparator
  和 encoded sequence side tag 执行 bounded search、bump/free-list allocation 与完整 RB
  fixup。两个 512-node books 各自填满，每一步完整 32,800 bytes 都与 `lib-sokoban 0.3.0`
  一致；满树 duplicate 只替换 value，满树新 key 与 malformed/readonly/wrong owner 均原子
  失败。持久状态仍只有 one-based index / `0` sentinel，不使用 heap/Map、detached node 或
  persistent pointer。当前 digest `2a24252f935ac912`，assembly 4,528,527 B，ELF
  1,448,496 B，IDL 6,647 B；Surfpool 1.5.0 以 1,432 个 Loader write transactions 部署并
  核对 exact 1,448,541-byte ProgramData。本轮 194-job Lean、50 个 SVM build、Mollusk
  225/225 和 Anvil 12/12 全绿。
- P5 第二十段 fixed-capacity bid/ask removal 已完成：通用
  `accDataRbTreeOrderRemove` 在完整 tree/free-list preflight、encoded sequence side tag 与
  key lookup 后，按 Sokoban 0.3.0 原位执行 predecessor transplant、bounded delete-fixup
  和 free-list push。两个满载 512-node books 各自按独立 permutation 逐个删空，每一步
  完整 32,800 bytes 都与官方实现一致；随后各 16 次 insertion 也精确复用同一 LIFO
  free-list。missing/malformed/readonly/wrong owner 全部在 store 前原子失败。持久状态仍
  只有 one-based index / `0` sentinel，不使用 heap/Map、detached node 或 persistent
  pointer。当前 digest `8290f8143ffc2374`，assembly 4,616,716 B，ELF 1,477,344 B，IDL
  7,210 B；Surfpool 1.5.0 以 1,460 个 Loader write transactions 部署并核对 exact
  1,477,389-byte ProgramData。本轮 194-job Lean、50 个 SVM build、Mollusk 228/228 和
  Anvil 12/12 全绿。
- P5 第二十一段 fixed-capacity trader deposit 已完成：通用
  `accDataRbTreeTraderDeposit` 按官方 18-word node / 12-word `TraderState` 布局，在完整
  tree/free-list preflight 后执行 Pubkey get-or-register。已有 trader 的 quote/base free
  lots 在两个 checked-add 均成功后才一起写回；新 trader 的完整 slot 先清零再初始化，
  满树 existing-key 仍成功而 absent-key 返回 full。128 个 trader 在每个 allocator size
  重复 deposit，每一步完整 18,464 bytes 均与 `lib-sokoban 0.3.0` 一致；两类 overflow、
  malformed/readonly/wrong owner 全部原子失败。持久状态只有 one-based index / `0`
  sentinel，不使用 heap/Map、detached node 或 persistent pointer。当前 digest
  `e9966de4a1795a47`，assembly 4,652,382 B，ELF 1,489,088 B，IDL 7,613 B；Surfpool
  1.5.0 以 1,472 个 Loader write transactions 部署并核对 exact 1,489,133-byte
  ProgramData。本轮 194-job Lean、50 个 SVM build、Mollusk 230/230 和 Anvil 12/12 全绿。
- P5 第二十二段 account-resident storage backend boundary 已完成：新增 target-owned
  `Svm.AccountStorage`，以编译期固定 `Region/Field`、显式 zero/one-based indexing、generic
  value traversal/canonicalization 与 transitive `EffectSummary` 承载 persistent container
  routine。`accDataWordSetAt` 已从顶层 SVM Ops/IR 和主 emitter 的 bespoke case 迁入单一
  `.accountStorage` bridge；主 emitter 只注入 value loader、owner check 与 walked-account
  frame，IDL writable meta 由 storage effect 推导。source spelling、digest
  `e9966de4a1795a47`、ELF 1,489,088 B 与 IDL 7,613 B 均保持不变。该层不引入 heap
  allocation、runtime capacity、Map、detached node 或 persistent pointer。本轮 196-job
  Lean、50 个 SVM build、Mollusk 230/230、Anvil 12/12 全绿；Surfpool 1.5.0 以 1,472 个
  Loader write transactions 部署并核对 exact 1,489,133-byte ProgramData。下一步先迁移
  bounded parent-path，再收拢 RB search/allocator/rotation/transplant/fixup。
- P5 第二十三段 bounded account-storage query bridge 已完成：
  `accDataParentPathValid` 迁入 `AccountStorage.Query.parentPathValid`；两个 fixed-stride
  `Field` 统一声明 one-based region、read-only effects、三参数 arity、geometry/depth bound、
  account walk 与 canonical spelling。SVM `ValKind`、generic extraction traversal、IR digest
  与主 `loadVal` 都只保留单一 `.accountStorage query` bridge，原 138 行 parent-path emitter
  已移入 storage backend。source 名称与 digest `e9966de4a1795a47` 保持；assembly
  4,652,144 B、ELF 1,489,088 B、IDL 7,613 B 均不变。路径仍只保存当前 one-based index、
  depth 和 account-derived transient pointer，不使用 heap/Map、visited collection、node copy
  或 persistent pointer。本轮 196-job Lean、50 个 SVM build、Mollusk 230/230、Anvil
  12/12 全绿；Surfpool 1.5.0 以 1,472 个 Loader write transactions 部署并核对 exact
  1,489,133-byte ProgramData。下一步迁移 complete RB validator 的共同 envelope 与内部例程。
- P5 第二十四段 FIFO RB-tree account-storage query 已完成：bid/ask 共用的 complete
  `accDataRbTreeValid` 已迁入 `AccountStorage.Query.fifoRbTreeValid`；links、parent/color、
  price、sequence 四个 fixed-stride `Field` 统一声明 one-based region、read-only effects、
  四参数 arity、4096-slot capacity bound 与 canonical spelling。原 449 行完整 tree/free-list
  validator 已从主 emitter 移入 storage backend，order insert/remove preflight 也组合调用
  同一 Query routine；`ValKind`、generic extractor、IR canonicalization 与主 `loadVal` 不再有
  FIFO validator 特判。实现继续只用 fixed 4096-bit frame bitmap、one-based index 和 `0`
  sentinel，不使用 heap/Map、node copy、runtime geometry 或 persistent pointer。digest
  `e9966de4a1795a47`、assembly 4,652,144 B、ELF 1,489,088 B 与 IDL 7,613 B 保持不变；
  196-job Lean、50 个 SVM build、Mollusk 230/230、Anvil 12/12 全绿，Surfpool 1.5.0
  以 1,472 个 Loader write transactions 部署并核对 exact 1,489,133-byte ProgramData。
  下一步迁移 four-word Pubkey validator 并抽取共同 topology/allocator layout。
- P5 第二十五段 Pubkey RB-tree account-storage query 已完成：four-word
  `accDataRbTreeKey4Valid` 已迁入 `AccountStorage.Query.key4RbTreeValid`；FIFO 与 Pubkey
  layout 共用编译期固定的 `RbTree` links/parent-color topology 和 64-edge traversal bound，
  Pubkey query 另声明连续四字 key region 与 8321-slot capacity bound。trader insert/remove/
  deposit preflight 组合调用同一个 Query routine，顶层 `ValKind`、主 `loadVal` 和 IR
  canonicalization 不再有 Pubkey validator 特判。完整 tree/free-list 验证仍只使用 fixed
  8321-bit frame bitmap、64-entry stack、one-based index 与 `0` sentinel，不引入 heap/Map、
  runtime geometry、node copy 或 persistent pointer。source digest `e9966de4a1795a47`、
  assembly 4,652,144 B、ELF 1,489,088 B 与 IDL 7,613 B 保持不变；196-job Lean、50 个
  SVM build、Mollusk 230/230、Anvil 12/12 全绿，Surfpool 1.5.0 以 1,472 个 Loader write
  transactions 部署并核对 exact 1,489,133-byte ProgramData。下一步把 bounded search、
  allocator acquire/release、rotation/transplant/fixup 迁为 storage mutation routines。
- P5 第二十六段 bounded account-storage map mutation vocabulary 已完成：原 five 个
  trader/order bespoke mutation constructors 已从顶层 `Svm.OpExt`、`Svm.IR.Op` 和主 emitter
  dispatch 删除，收敛为 `AccountStorage.Call` 的 `rbMapInsert`、`rbMapRemove` 与
  `rbMapCheckedAdd`。`RbMap` descriptor 统一拥有编译期固定 account/header/topology/key/value
  geometry、capacity、one-based indexing、writable/current-owner access 与 duplicate policy；
  extraction、CFG、signer/account inference、IDL writable inference 和 canonicalization 只遍历
  generic values/effects。现有原位 assembly 由 storage mutation backend adapter 复用，source
  digest `e9966de4a1795a47`、assembly 4,652,144 B、ELF 1,489,088 B 与 IDL 7,613 B 均不变。
  持久状态仍不使用 heap/Map、runtime geometry、node copy、detached node 或 persistent
  pointer。196-job Lean、50 个 SVM build、Mollusk 230/230、Anvil 12/12 全绿；Surfpool
  1.5.0 以 1,472 个 Loader write transactions 部署并核对 exact 1,489,133-byte
  ProgramData。下一步把 search/allocator/rotation/transplant/fixup assembly 实体迁入 backend。
- P5 第二十七段 bounded account-storage field extractor 已完成：runtime-indexed
  `accDataWordAt` 已从独立 SVM `ValKind` 和主 `loadVal` case 迁入
  `AccountStorage.Query.readWord`。统一 `Field` descriptor 携带编译期固定 account/base/stride/
  capacity 与 zero/one-based indexing；one-based 模式拒绝 `0` sentinel 后再归一化，供后续
  map lookup 返回 index 直接组合。query 自己拥有 arity、read-only effects、account inference
  与 `dwi`/`dwi1` canonical spelling，source helper 和 wire ABI 不变。实现只在 index 与最终
  data length 检查后形成调用期 transient pointer，不分配 heap/Map、不复制 node、不开放
  runtime geometry 或 persistent pointer。source digest `e9966de4a1795a47` 保持，迁移前后
  4,652,144-byte assembly 逐字节相同；ELF 1,489,088 B、IDL 7,613 B 不变。196-job Lean、
  50 个 SVM build、Mollusk 230/230、Anvil 12/12 全绿；Surfpool 1.5.0 以 1,472 个 Loader
  write transactions 部署并核对 exact 1,489,133-byte ProgramData。下一步增加 bounded
  Key4/FIFO map-find query，再组合 field read/write/remove 实现 ReduceOrder。
- P5 第二十八段 bounded account-storage RB map find 已完成：`Query.fifoFind` 与
  `Query.key4Find` 复用同一个 storage-owned `emitRbFind`，按编译期固定 root/links/key/
  stride/capacity 在 account bytes 中直接搜索，返回 one-based node index 或 `0`。Key4 用
  `be64` 保持 `[u8;32]` byte ordering；FIFO ask 升序、bid 降序。每个 dereference 都检查
  `1..capacity`，统一 64-level bound 拒绝 cycle/过深输入；account 0 与 walked external
  account 都先做覆盖 root/links/key 的 data-length gate。validator/find/mutable map 现在共用
  `FifoRbTree.oneBased` / `Key4RbTree.oneBased` layout constructors；query 自己拥有 arity、
  read-only effects、account inference 与 `rbof`/`rb4f` canonical spelling，主 `loadVal` 没有
  新 case。实现只保留 scalar index/depth 和调用期 transient pointer，不分配 heap/Map、
  bitmap，不复制 node，不开放 runtime geometry。isolated Key4/FIFO programs 经 `sbpf build`
  产出 3,720 B / 3,480 B ELF；196-job Lean、50 个 SVM build、Mollusk 230/230、Anvil
  12/12 与 Surfpool smoke 全绿。下一步接 Runtime/source intrinsic，再组合
  find/read/write/remove 实现 ReduceOrder。
- P5 第二十九段 source-level bounded RB find 已完成：新增薄
  `accDataRbTreeKey4Find` / `accDataRbTreeOrderFind` Runtime decoder，所有 account/root/field/
  stride/capacity/bid geometry 必须是 extraction-time constant，dynamic 参数只有 Key4 四词或
  FIFO `(price, sequence)`。decoder 直接构造 `AccountStorage.Query` 并复用 well-formed gate，
  没有新增顶层 Op/IR/主 Emit case。PhoenixV1Profile 的 `findTrader128`、`findBid512`、
  `findAsk512` 先组合 complete tree/free-list validator，再执行共同 64-level bounded search，
  found 返回 exact one-based slot，missing 或 malformed topology 返回 `0`；三个 IDL account
  metas 都是 read-only。Mollusk 覆盖 trader/bid/ask found/missing 与 malformed self-cycle；
  持久状态仍无 heap Map、node copy、detached allocation 或 pointer。当前 digest
  `b37d4fce03b21ff4`，assembly 5,638,878 B，ELF 1,799,856 B，IDL 8,370 B；196-job
  Lean、50 个 SVM build、Mollusk 231/231、Anvil 12/12 与 Surfpool 1.5.0 Loader-v3 smoke
  全绿。下一步组合 find/read/write/remove 实现 official ReduceOrder semantics。
- P5 第三十段 composed ReduceOrderWithFreeFunds state transition 已完成：source 新增薄
  `accDataWordAtOneBased` / `accDataWordSetAtOneBased`，直接落入既有 AccountStorage
  read/write descriptor，不新增顶层 ValKind/Op/IR/主 Emit case。最小 official profile 的
  ask/bid reducer 组合 complete trader/order validator、signer Pubkey Key4 find、FIFO find、
  one-based field read/write 与 full `rbMapRemove`；missing 成功 no-op，wrong trader 失败，
  partial 原位改 quantity，full 回收固定节点。ask 解锁 base lots；bid 按
  `price × tick × removed / baseLotsPerBaseUnit` 解锁 quote lots，所有除零、乘法、余额
  subtraction/addition 在第一条 store 前 preflight。持久状态仍只有 one-based index / `0`
  sentinel，无 heap Map、node copy、detached allocation 或 persistent pointer。当前 digest
  `fdec3afb265a542`，assembly 6,548,227 B，ELF 2,081,880 B，IDL 9,011 B；196-job Lean、
  50 个 SVM build、Mollusk 232/232、Anvil 12/12 与 Surfpool 1.5.0 Loader-v3 smoke 全绿。
  下一步独立接 tag 5 wire/account/event adapter，再实现 tag 4 Token withdrawal。
- P5 第三十一段 reusable packed SVM entry adapter 已完成：Core annotation 只携带 opaque
  target metadata，不新增 executable Ops；`Svm.EntryAdapter` 在 target projection 后统一拥有
  u8 tag dispatch、exact packed u8/u16/u32/u64 widening、bounded account-prefix walk、当前
  executable program authentication 与 raw/generated route。raw 方法不得把 physical program
  account 当 managed State，持久读写必须组合 `AccountStorage`；IDL 排除 protocol-owned raw
  wire，Legacy downgrade 显式拒绝 metadata loss。`Examples.RawEntry` 的同一 ELF 验证 raw
  与 generated ABI 共存；Mollusk 覆盖 exact/short/long/tag/signer/program/trailing-account
  matrix，Surfpool 1.5.0 用 4 个 Loader write transactions 部署 3,064-byte ELF 并核对 exact
  ProgramData；200-job Lean、51 个 SVM build、Mollusk 238/238、Anvil 12/12 全绿。下一步只用
  这层组合 Phoenix tag 5 wire/account/event，不向主 Emit 添加 Phoenix 分支。
- P5 第三十二段 official Phoenix-v1 tag 5 已完成：source 以 exact 26-byte
  `05 || side:u8 || price:u64-le || sequence:u64-le || size:u64-le` wire 和 current program / readonly
  canonical `"log"` PDA / writable market / readonly trader signer 四账户进入；generated probes 与
  raw handler 复用同一组 extraction-time account-index-parametric `AccountStorage` reducer，没有
  新增 Phoenix-specific top-level op、IR node 或主 Emit case。ask/base 与 bid/quote collateral 的
  partial update、full RB-tree removal/free-list reuse、missing-order sequence-only transition 和
  existing-order exact 128-byte authenticated self-CPI event 均已由 Mollusk 固定；tag 5 不触发
  Token CPI。raw external-account index 明确排除 physical program prefix；SVM frame 也固定为
  account-storage scratch ≤408、headers 512..、scalar locals <1024、CPI 1024..2048、deep scratch
  2048..4096，并对超过 1,024-byte 的完整 CPI frame fail closed。PhoenixV1Profile digest 为
  `c6d4dd40cfd7b340`；artifact 为 7,504,658-byte assembly / 2,375,160-byte ELF /
  9,011-byte IDL；200-job Lean、51 个 SVM build、Mollusk 242/242、Anvil 12/12 全绿；Surfpool
  1.5.0 以 2,347 个 Loader-v3 writes 部署并核对 exact 2,375,205-byte ProgramData。详见
  `docs/plan/tasks/l5-039.md`。下一步实现 official tag 4 Token withdrawal。
- P5 第三十三段 official Phoenix-v1 tag 4 已完成：`ReduceOrder` 复用 tag 5 的
  account-index-parametric `AccountStorage` reducer，只在九账户 `EntryAdapter` 边界增加官方
  reduce-status 与 classic Token context validation。ask/base 与 bid/quote 都只 claim 本次
  release，不动既有 free balance；非零 atoms 通过通用 unchecked tag-3 transfer，以
  `["vault", market key, MarketHeader mint bytes, bump]` 签名。新的 `.accData` PDA seed
  直接引用经过 data-length gate 的固定 ≤32-byte account slice，不分配或复制。通用抽取器
  现在把账户 read 的 lexical `let` 在后续 effect 前 materialize，并保留 ignored inline
  helper 的控制流/effect continuation，因此 audit header 使用 pre-increment sequence；
  existing/missing order 分别产生 exact 128/93-byte batch。tag 5 的 reducer 不再错误继承
  tag 4 status gate。没有新增 Phoenix-specific 顶层 Op、IR node 或主 Emit case；持久状态
  仍只有 one-based index / `0` sentinel。当前 digest `987f4a8231f46f75`，assembly
  9,072,964 B、ELF 2,855,072 B、IDL 9,011 B；200-job Lean、51 个 SVM build、
  Phoenix-v1 profile 42/42、全 Mollusk 246/246 与 Anvil 12/12 全绿。Surfpool 1.5.0
  以 2,822 个 Loader-v3 writes 部署并核对 exact 2,855,117-byte ProgramData。详见
  `docs/plan/tasks/l5-040.md`。下一步先提供 storage-owned ordered cursor 与 bounded audit
  batching，再在其上组合无 payload 的 tag 6/7 CancelAll pair。
- P5 第三十四段 storage-owned ordered cursor 已完成：`Query.fifoCursor` 在 target-owned
  `AccountStorage` 内拥有固定 account/root/links/key/stride/capacity/bid geometry、三操作数
  arity、read-only effects、account inference、well-formed gate 与 `rboc` canonical spelling。
  `hasCursor=0` 返回逻辑 first one-based slot；`hasCursor=1` 从保留的 scalar
  `(price, sequence)` 做 strict upper-bound；empty/end 返回 `0`。每次都从 root 重新查询，
  mutation 前后不保存 node address；ask 升序、bid 降序和 equal-price FIFO 都复用现有比较器。
  查询只保留 current/candidate/depth scalars，逐 link 检查 `1..capacity`，64-level bound 与完整
  account envelope 拒绝 cycle、越界和短数据；`hasCursor > 1` 失败。薄 Runtime/Ops/Extract
  helper 强制全部 geometry 为 extraction-time constants；没有新增顶层 Op/IR/主 Emit case，
  也没有 heap Map/Vec、node copy、runtime geometry 或 persistent pointer。profile read-only
  probe 覆盖 empty/first/strict next/in-between/equal-price/end、删除后重查和 malformed cycle。
  当前 digest `c464e5b76446904d`，assembly 9,733,659 B、ELF 3,062,480 B、IDL 9,537 B。
  200-job Lean、51 个 SVM build、Phoenix profile 43/43、全 Mollusk 247/247 与 Anvil 12/12
  全绿；Surfpool 1.5.0 以 3,027 个 Loader-v3 writes 部署并核对 exact 3,062,525-byte
  ProgramData，不使用 Test Validator。
  详见 `docs/plan/tasks/l5-041.md`。下一步提供 reusable bounded audit recorder/batching，
  再组合 tags 6/7 CancelAll。
- P5 第三十五段 generic bounded SVM component bridge 已完成：新增
  `Svm.Component.Query/Call` 与 component-owned Emit context/backend，把原顶层
  `.accountStorage` value/effect/IR case 收进唯一 `.component` bridge。generic extraction、
  target projection、CFG payload、value traversal、account/signature inference、IDL writable
  inference 与主 emitter 不再枚举具体 storage/queue/recorder/allocator；新增 bounded feature
  只扩 component-owned vocabulary/backend。AccountStorage 的 Region/Field/index、effects、
  well-formedness、canonical spelling 与 emitter 原样委托，source spelling 和 runtime 语义
  不变。当前 digest `c464e5b76446904d`、assembly 9,733,659 B、ELF 3,062,480 B、IDL
  9,537 B 均保持。持久结构仍只用 fixed account bytes、one-based index 与 `0` sentinel；
  不开放 heap Map/Vec、runtime geometry、detached node 或 persistent pointer。详见
  `docs/plan/tasks/l5-042.md`。下一步在该 bridge 内实现 bounded audit recorder/batching，
  再组合 tags 6/7 CancelAll。本轮 202-job Lean、51 个 SVM build、Mollusk 247/247 与
  Anvil 12/12 全绿。
- P5 第三十六段 bounded invocation-local audit recorder 已完成：在唯一
  `Svm.Component.Call` bridge 内增加 begin/append/finish 与 component-owned dynamic signed
  self-CPI sink；generic Ops/IR/CFG/主 Emit 不增加 recorder case。payload 与官方 Rust SDK
  allocator 协调同一个 `0x300000000` 首-word cursor，固定按 SDK 的 32 KiB end 向下 bump、
  8-byte align，OOM 不提交 cursor；不假设 Agave 可选的大 frame，也不把地址暴露给 source
  或持久账户。Phoenix header 为 93 B、Reduce 为 35 B、inner data 上限为
  `1280 - 34 = 1246 B`；32 条共 1,213 B，第 33 条 append 前自动 flush，finish 即使零事件
  也发 header-only batch。stack metadata 只占 416..448，scalar-local planner 按实际 component
  capability 求 max，未使用 recorder 的程序保持旧 408 boundary。tag 4/5 已迁移到 recorder，
  existing/missing output 仍由 Mollusk 固定为 exact 128/93 B。当前 digest
  `79102f84e2217820`，assembly 9,708,793 B、ELF 3,052,280 B、IDL 9,537 B；205-job Lean、
  51 个 SVM build、Phoenix profile 43/43、全 Mollusk 247/247 与 Anvil 12/12 全绿；
  Surfpool 1.5.0 以 3,017 个 Loader-v3 writes 部署同一 ELF，并核对 exact
  3,052,325-byte ProgramData。详见
  `docs/plan/tasks/l5-043.md`。下一步直接组合 tags 6/7 CancelAll；persistent Queue/Map/
  Allocator 仍必须使用 fixed account bytes、one-based index 和 `0` sentinel。
- P5 第三十七段 official Phoenix-v1 tags 6/7 CancelAll 已完成：新增 target-owned
  `FifoCancel` component，在一个完整 trader/bid/ask tree/free-list validator 之后，组合
  storage-owned strict-successor cursor、one-based owner/size/balance fields、内部
  validated RB removal 与现有 `BatchRecorder`。每次 mutation 后只凭 scalar
  `(price, sequence)` 从 root 重查；不保存 node address，不收集 heap `Vec/Map`，也不把
  pointer 写入账户。tag 7 使用 exact one-byte wire / 四账户且不进入 Token/status gate；
  tag 6 使用九账户 classic Token context，只 claim 本次释放量并按 quote claim/withdraw →
  base claim/withdraw。两者均先 bids 后 asks、各侧保持官方 FIFO、按 trader owner 过滤；
  global u16 event index 跨 32-record recorder flush 连续，missing trader/empty books 仍
  sequence+1 并发 93-byte header-only batch。generic Ops/IR/CFG/主 Emit 仍只有单一
  `.component` bridge；source 无法选择 validated-remove 内部 hook。当前 digest
  `5c4cc53d053d7035`，assembly 10,920,313 B、ELF 3,433,400 B、IDL 9,537 B，ELF
  SHA-256 `797cfa1a599ae704140e06fb29f1230df5d211bd993224c961922e3eced8d3c6`。
  207-job Lean、51 个 SVM build、Phoenix profile 51/51、全 Mollusk 255/255 与 Anvil
  12/12 全绿。Surfpool 1.5.0 以 3,393 个 Loader-v3 writes 部署同一 ELF，并核对 exact
  3,433,445-byte ProgramData；未使用 `solana-test-validator`。详见
  `docs/plan/tasks/l5-044.md`。下一步在同一 component/entry-adapter 边界实现 tags 8/9
  CancelUpTo 的 Borsh Option payload 与 bounded side/price/search/cancel filter，不扩张顶层
  Ops/IR/主 Emit。
- P5 第三十八段可复用变长 Borsh Option entry plan 已完成：新增
  `@[pf_svm_raw_borsh_options ...]` / `svm.raw.v2`，将固定 scalar prefix 与编译期定宽的
  `Option` 字段投影到 target-owned `EntryAdapter.RawEntry`，由 adapter 自己生成 finite
  min/max route、canonical 0/1 discriminant、`Some` payload end-bound 和最终 exact cursor
  consumption；invalid discriminant、truncated payload 与 trailing bytes 全部 fail closed。
  executable current-program 检查按实际 instruction length 动态定位，fixed/variable wire
  共用同一认证路径；generic Ops/IR/CFG/主 Emit 没有新增 codec op。`RawEntry` probe 覆盖
  `side:u8 + Option<u64> + Option<u32> + Option<u32>` 的全部 8 种 presence 组合和完整 malformed
  matrix，digest `74fced960b29aba0`，assembly 15,171 B、ELF 5,088 B、IDL 1,033 B，ELF
  SHA-256 `dcb49ec81a41665c89101c84f91dc782edda062e3fde7f14c4ad51a10c17d763`。
  207-job Lean、51 个 SVM build、RawEntry 8/8 与 Phoenix profile 51/51 全绿。Surfpool 1.5.0
  以 6 个 Loader-v3 writes 部署同一 ELF，并核对 exact 5,133-byte ProgramData；未使用
  `solana-test-validator`。详见 `docs/plan/tasks/l5-045.md`。下一步直接复用该 plan 与现有
  `FifoCancel` component 实现 official Phoenix-v1 tags 8/9，不扩张顶层 Ops/IR/主 Emit。
- P5 第三十九段 official Phoenix-v1 tags 8/9 CancelUpTo 已完成：复用 variable Borsh
  entry plan 的 exact `tag || side:u8 || Option<u64> || Option<u32> || Option<u32>` wire，并只在
  target-owned `FifoCancel.Call` 增加 bounded `cancelUpTo`；generic executable Ops/IR/CFG/主
  Emit 继续只有一个 `.component` bridge。组件复用 account-storage strict-successor cursor，
  每个 cursor result 在 owner/price filter 前计入 search，只有 selected order 计入 cancel；
  bids 用 inclusive `price >= tick`，asks 用 inclusive `price <= tick`，equal-price FIFO 不变，
  capacity/search/cancel 三重边界均在 emitter 内 fail closed。`None` tick 使用 side extreme，
  `None` search/cancel 使用 selected book 当前 size；missing trader、no match 与显式零仍
  sequence+1 并发 header-only batch。tag 9 四账户、无 Token/status gate并保留 free funds；
  tag 8 九账户、逐单 claim 以保留 pre-existing free，再只提款 selected side aggregate。
  持久 Queue/Map/Allocator 仍只使用 fixed account bytes、one-based index 与 `0` sentinel；
  不引入 heap `Vec/Map`、copied/detached node、persistent pointer、runtime geometry 或无界遍历。
  当前 digest `afe3c027d0f83661`，assembly 12,091,217 B、ELF 3,796,416 B、IDL 9,537 B，
  ELF SHA-256 `d8dc3ebdbdfe4d01a3b0aa314248418c4772d098c07a772f5f728bf599a8fef6`。
  207-job Lean、51 个 SVM build、Phoenix profile 60/60、全 Mollusk 266/266 与 Anvil 12/12
  全绿。Surfpool 1.5.0 以 3,752 个 Loader-v3 writes 部署 byte-identical ELF，并核对 exact
  3,796,461-byte ProgramData；未使用 `solana-test-validator`。详见
  `docs/plan/tasks/l5-046.md`。下一步保持 component bridge 不变，分片识别并组合
  matching/placement ABI；remaining accounts 作为独立 bounded adapter capability，不把协议
  语义或持久容器下沉成新的顶层 opcode。
- P5 第四十段 Phoenix sequence domain correction 已完成：官方
  `MarketHeader.market_sequence_number` 位于 absolute account word 34，而 FIFO body 的
  `order_sequence_number` 位于 word 106；此前 tags 4–9 错把后者当成 market sequence，既会
  污染后续挂单 key，也会让 audit header 携带错误序列。本切片把 profile view、六个 raw
  reduce/cancel route 的 pre-increment audit sequence 与写回统一迁到 word 34，并用独立
  fixtures 证明每条 route 都只递增 market sequence、保持 word 106 不变。word 106 仍由
  storage envelope 验证为已初始化 FIFO order sequence；修正不改变 EntryAdapter、Component、
  AccountStorage 或 generic Ops/IR/CFG/主 Emit 边界。当前 digest `ad2734feeb8c49dd`，assembly
  12,091,190 B、ELF 3,796,416 B、IDL 9,537 B，ELF SHA-256
  `96086af4bbcaaff2aa05b1ad92635ff4ea3576714433bd3986e00c3bfdce0821`。207-job Lean、
  51 个 SVM build、Phoenix profile 60/60、全 Mollusk 266/266 与 Anvil 12/12 全绿；
  Surfpool 1.5.0 以 3,752 个 Loader-v3 writes 部署 byte-identical ELF，并核对 exact
  3,796,461-byte ProgramData；未使用 `solana-test-validator`。详见
  `docs/plan/tasks/l5-047.md`。下一步在固定 bridge 上实现 official tag 3 的严格
  PostOnly/no-TIF/deposited-funds-only 子集，再把完整 OrderPacket enum/option decoding
  收敛成 EntryAdapter schema 数据，而不是新增 codec opcode。
- P5 第四十一段 official Phoenix-v1 tag 3 严格 PostOnly placement 已完成：新增 exact
  40-byte `OrderPacket::PostOnly` wire 与五账户认证，canonical log/seat PDA、Phoenix-owned
  128-byte approved seat 及其 market/trader identity 在任何 storage effect 前 fail closed。
  成功路径组合既有 complete trader/bid/ask validator、one-based trader find、FIFO
  find/insert、balance word-store 与 BatchRecorder；买单复用共享 quote-lot geometry 把 free
  quote 转 locked，卖单把 free base 转 locked。当前严格边界要求 Active/PostOnly status、
  opposite book empty、selected book 有容量、无 TIF、deposited funds only、hard funds failure，
  因而不伪装 matching/reprice/expiry/eviction。word 106 只生成并递增 FIFO order sequence，
  word 34 独立生成 audit sequence；43-byte Place record 保留 u128 client id 的两个 LE limbs。
  generic Ops/IR/CFG/主 Emit 与 Component vocabulary 均未新增 case，持久状态继续只有 account
  bytes、one-based index 和 `0` sentinel。当前 digest `4a74bafb995ad60a`，assembly
  12,636,870 B、ELF 3,960,464 B、IDL 9,537 B，ELF SHA-256
  `abdd4b5af17be9e6b363a52365ce200f3a1ee8d2fc759c2cd7b5b2a0c5665311`。207-job Lean、
  51 个 SVM build、Phoenix profile 65/65、全 Mollusk 271/271 与 Anvil 12/12 全绿；
  Surfpool 1.5.0 以 3,914 个 Loader-v3 writes 部署 byte-identical ELF，并核对 exact
  3,960,509-byte ProgramData；未使用 `solana-test-validator`。详见
  `docs/plan/tasks/l5-048.md`。下一步先把 effectful raw scalar return 泛化成 bounded scalar
  tuple，直接复用现有 CFG `returnU64s` / SVM `sol_set_return_data`，再用固定宽度 codec 补齐
  tag 3 官方单元素 Borsh `Vec<FIFOOrderId>` 的 20-byte return；随后把完整 OrderPacket 继续
  收敛成 EntryAdapter schema。
- P5 第四十二段 bounded effectful scalar tuple 已完成：抽取层把静态 Lean `Prod` 递归摊成
  已有 scalar leaves，单值继续使用 `okState`，多值只生成既有 `returnU64` sequence；Core
  CFG 自动汇合为 `returnU64s`，SVM 复用 fixed eBPF stack scratch 与
  `sol_set_return_data(compile_time_bytes)`。没有新增 Core/SVM Op、IR、CFG、EntryAdapter、
  Component 或主 Emit case；product/Array 只存在于编译期，不产生链上 heap `Vec/Map`、
  allocator call 或 pointer。独立 RawEntry tag 9 固定两 u64 的 16-byte scalar tuple；tag 10
  以通用 `[4,8,8]` codec 固定单元素 Borsh pair 的 exact 20 bytes。Phoenix tag 3 现返回
  官方 `length=1:u32 || price:u64 || encoded_sequence:u64`，bid/ask exact bytes 已与原
  storage/audit assertions 同时固定；profile digest
  `9ecc2b7df3ecde85`、assembly 12,638,154 B、ELF 3,960,600 B、IDL 9,537 B，Mollusk
  65/65；Surfpool 1.5.0 用 3,914 writes 核对 byte-identical ELF 与 exact 3,960,645-byte
  ProgramData。RawEntry digest `cefd717563a8ea95`，assembly 21,726 B、ELF 7,128 B、IDL
  1,033 B，Mollusk 10/10；Surfpool 用 8 writes 核对 exact 7,173-byte ProgramData。213-job
  Lean 与 51 个 SVM build 全绿；远端已有 EVM Token solc 0.8.34
  StackTooDeep 门单独保持红色，不归因于本切片。详见 `docs/plan/tasks/l5-049.md`。下一步
  固定该返回层不再改主 Emit。通用 `AccountStorage.Source` 进一步把 field/key4/FIFO 的
  静态 handles 与动态 key/value 分开；Phoenix 512/512/128 的具体 offsets/capacities 只在
  `Examples/PhoenixV1Layout.lean` 实例化，`ProofForge/Svm` 与 Extract 均不认识 Phoenix
  namespace。其余 official `OrderPacket` 再逐 variant 收敛成 bounded EntryAdapter schema，
  并按切片增加 component-owned matching；未实现语义继续 fail closed。
- P5 第四十三段 Phoenix source ownership 已收口：完整 bounded host model 与 official-account
  profile/handlers 从 `Projects` 迁到 `Examples.Phoenix` / `Examples.PhoenixV1Profile`，不是删除
  已实现的 allocator/tree/order/cancel/reduce/recorder 行为。`Projects` Lake library、root import
  与 CLI program-name 特判均已删除，51 个 SVM program 统一按 `Examples.<Name>` 加载；测试、
  legacy fixture 与文档同步改 namespace。Phoenix / profile canonical digest 仍分别为
  `ec8383cf470795f4` / `9ecc2b7df3ecde85`，profile ELF SHA-256 仍为
  `af27cf67566458007c5131aff69cad70101de56f8074c9e5b38973e7bbdce660`，与 L5-049 已经
  Surfpool 1.5.0 部署的 bytes 相同。核心 `ProofForge/Svm` 仍无 Phoenix 名字、offset 或专用
  Emit case。详见 `docs/plan/tasks/l5-050.md`。下一步先迁移 reduce/cancel/recorder 的其余
  positional geometry 到命名静态句柄，再扩 OrderPacket/matching。
- P5 第四十四段 static storage component facade 已完成：通用
  `AccountStorage.Source.validate` 现在只接收编译期 `RbMap` handle，由 facade 内部拥有
  allocator header 的 root/size/cursor、packed cursor 拆分、stride/capacity、key shape 与 bid
  ordering；Phoenix source 不再拼 validator geometry。`Examples.PhoenixV1.Layout` 集中
  已迁移 512/512/128 路径的 offsets/capacities，并提供命名 header、book、order、trader
  balance 与 mutation API；bid/ask free-funds reducer 及 raw reduce/claim/withdraw adapter
  已改为组合这些 API，尚未迁移的 cancel/recorder positional geometry 留给下一切片。
  Extract 只把 validator geometry 从 direct literal 泛化成 static literal；没有新增
  Phoenix 特判、顶层 Ops/IR/Component/主 Emit case，也没有 heap Map/Vec、runtime geometry、
  persistent pointer 或无界遍历。旧 `Projects` 路径已完全不存在。当前 digest
  `588c0d478800f7de`，assembly 12,645,217 B、ELF 3,963,800 B、IDL 9,537 B，ELF SHA-256
  `7edc297917766ebe73dbd316e090fd321a1f4898832713db60362a5738f51cb2`。213-job Lean、
  51 个 SVM build 与 Phoenix profile Mollusk 65/65 全绿；Surfpool 1.5.0 以 3,917 个正常
  Loader-v3 writes 部署并核对 exact 3,963,845-byte ProgramData，未使用 Test Validator。
  详见 `docs/plan/tasks/l5-051.md`。下一步把 cancel-all/trader lookup/FifoCancel positional
  geometry 迁到同一 layout/component facade，再收口 recorder profile，最后扩
  OrderPacket/matching。
- P5 第四十五段 static FIFO cancellation facade 已完成：新增通用
  `ProofForge.Svm.FifoCancel.Source`，以编译期 `FifoCancel.Config` 统一提供 begin、整侧
  cancel、bounded cancel-up-to、aggregate query 与 finish；抽取时 descriptor 被擦除到既有
  component/runtime 调用，只有 trader/tick/search/cancel scalar 保持动态，claim policy 必须是
  static Bool。`Examples.PhoenixV1.Layout` 现在集中组合 bid/ask book、trader locked/free、
  collateral/header words 与静态 audit sink；四条 official cancel handler 不再传 positional
  book/trader/recorder geometry。Phoenix offsets 与协议选择仍只在 `Examples`，没有新增
  Core/SVM opcode、顶层 IR、Component variant、CFG 或主 Emit case；链上持久状态仍只有固定
  account bytes、one-based index 与 `0` sentinel，没有 heap Map/Vec、copied node、persistent
  pointer、runtime geometry 或无界遍历。当前 digest `880a0a19f26dcdb3`，assembly
  12,658,267 B、ELF 3,967,864 B、IDL 9,537 B，ELF SHA-256
  `72a0e4b0895f3f8859de0dc5405b2f30d629f57a34e2c43a5cf55bd4e78212a8`。214-job Lean、
  51 个 SVM build 与 Phoenix profile Mollusk 65/65 全绿；Surfpool 1.5.0 以 3,921 个正常
  Loader-v3 writes 部署并核对 exact 3,967,909-byte ProgramData，未使用 Test Validator。
  详见 `docs/plan/tasks/l5-052.md`。下一步用同一 `marketRecorderConfig` 收口 recorder
  begin/append/finish source facade，再继续 bounded OrderPacket/matching。
- P5 第四十六段 static recorder facade 已完成：新增通用
  `ProofForge.Svm.BatchRecorder.Source`，以编译期 `BatchRecorder.Config` 提供 begin、append 与
  finish；抽取时 descriptor 被擦除到既有 component/runtime intrinsic，只有 header、record、
  enabled scalar 与 PDA bump 保持动态。Phoenix 的 audit header、Reduce/Place record 与
  finish helper 现在都复用 `Examples` 中的 `marketRecorderConfig`，不再向 handler 泄漏
  positional sink/byte geometry；同一 descriptor 也继续供 `FifoCancel.Source` 使用。
  Phoenix 协议、offset 与 wire record 仍只在 `Examples`，没有新增 Core/SVM opcode、顶层 IR、
  Component variant、CFG 或主 Emit case；invocation-local recorder buffer 仍由既有有界 bump
  allocator 持有，链上持久状态仍是固定 account bytes、one-based index 与 `0` sentinel，没有
  heap Map/Vec、persistent pointer、runtime geometry 或无界遍历。产物与上一切片 byte-identical：
  digest `880a0a19f26dcdb3`，assembly 12,658,267 B、ELF 3,967,864 B、IDL 9,537 B，
  ELF SHA-256 `72a0e4b0895f3f8859de0dc5405b2f30d629f57a34e2c43a5cf55bd4e78212a8`。
  215-job Lean、51 个 SVM build 与 Phoenix profile Mollusk 65/65 全绿；Surfpool 1.5.0 以
  3,921 个正常 Loader-v3 writes 部署并核对 exact 3,967,909-byte ProgramData，未使用 Test
  Validator。详见 `docs/plan/tasks/l5-053.md`。下一步保持 recorder/component/emitter 边界稳定，
  继续 bounded OrderPacket/matching。
- P5 第四十七段 reusable ordered storage + exact one-maker Limit matching 已完成：通用
  `AccountStorage` 新增 scalar/one-based field constructors、two-word ordered map、one-based
  allocator descriptor，以及 find/strict cursor/key/insert/remove/key4/allocator header source
  operations；legacy FIFO 名称只是同一表示的兼容 alias。Phoenix 的 `Book`、512/512/128
  layout、余额/费用字段、price-time/crossing/self-trade/audit policy 仍只在 `Examples` 组合，
  本切片没有向 generic Ops/IR/主 Emit 增加 Phoenix offset、matching opcode 或 matching
  branch。抽取器以 structural
  pure-facade reduction 取代 source namespace whitelist，并把后续写入前的 account read
  materialize 成 lexical local。`EntryAdapter` 以 `svm.raw.v4` schema 在同一 u8 tag 下路由
  distinct Borsh enum variant，精确验证 length/tag/discriminant 并消费 variant；RawEntry
  11/11 覆盖不同 payload shape 与 malformed matrix。tag 3 variant 1 现支持 exact 49-byte
  Limit 子集：`Abort`、`match_limit=Some(1)`、deposited funds、无 TIF、一个 non-self crossing
  maker 且 maker 被完整填满；bid/ask 两向余额、unclaimed quote fee、order removal、market
  sequence、67-byte Fill + 43-byte FillSummary 与当时实现的四字节 empty Borsh Vec return 均
  精确固定；下一切片将该协议偏差修为 official no-return behavior。partial
  fill、remainder/posting、multi-maker、eviction、其他 self-trade/match-limit/TIF/soft-funds
  policy 继续在任何 write 前 fail closed。当前 profile digest `52bb3c6e8d6cb9a9`，assembly
  13,311,498 B、ELF 4,165,728 B、IDL 9,537 B，SHA-256
  `befc073516944fd5f111f724ecb5988bbb96caba60e0a487f0429535d140df45`；229-job Lean、51 个
  SVM build、14 个 EVM build、Phoenix profile 68/68 与 Anvil 14/14 全绿。Surfpool 1.5.0
  以 4,117 个正常 Loader-v3 writes 部署并核对 exact ProgramData，未使用 Test Validator。
  详见 `docs/plan/tasks/l5-054.md`。下一步在相同 SDK/entry/component/emitter 边界上实现
  bounded partial-maker fill，再分别补 taker posting 与 multi-maker traversal。
- P5 第四十八段 reusable consume-in-place storage policy + partial maker fill 已完成：通用
  `AccountStorage` 新增 zero-remove/nonzero-update component；调用方传入同一 validated map view
  得到的 key、one-based slot 与新 scalar value，value 为零时复用 ordered-map remove/free-list，
  非零时 bounds-check 后写回原 fixed-stride slot，不保存 pointer。Phoenix 只在 `Examples`
  用它组合 `Book.setSizeOrRemove`，Limit 现可 bid/ask 双向原位 partial-fill 较大 maker，exact
  maker 仍删除；余额、aggregate taker fee、market sequence、Fill remaining 与 FillSummary 均
  精确固定。另新增 generic `svm.raw.v5` optional packed return：presence=0 成功但完全不调用
  `sol_set_return_data`，presence=1 序列化 fixed-width payload，其他值 fail closed；因此完整撮合
  且无 posted remainder 的官方 no-return 语义已修正，而不分配链上 Vec。generic SDK 不含
  Phoenix offset/matching policy，也没有持久 heap Map/Vec、runtime geometry、persistent pointer
  或无界遍历。当前 profile digest `4d6e0410bd14883f`，assembly 13,319,376 B、ELF
  4,167,368 B、IDL 9,537 B，SHA-256
  `15f4a90656e555f53a9b493d465c879a00f016ec490ee64d1216f9ddae46bf5f`；RawEntry digest
  `50563530f2356efc`。229-job Lean、51 个 SVM build、14 个 EVM build、RawEntry 11/11、
  Phoenix profile 70/70 与 Anvil 14/14 全绿。两个 exact ELF 均经 Surfpool 1.5.0 正常
  Loader-v3 transaction 部署核对，未使用 Test Validator。详见
  `docs/plan/tasks/l5-055.md`。下一步保持 component/optional-return 边界固定，先补
  one-maker 后 noncrossing remainder posting，再做 bounded multi-maker aggregate traversal。
- P5 第四十九段 bounded one-maker remainder posting 已完成：当较小 maker 被完整删除且 strict
  cursor 证明下一 opposite order 不再 crossing 时，Limit 把 taker remainder 插入己方固定
  512-slot book；bid 使用 complemented sequence，ask 使用 raw sequence，bid 按 taker limit
  price 锁 quote、ask 锁 remaining base。余额、aggregate taker fee、order/market sequence 与
  `Fill(0) → FillSummary(1) → Place(2)` audit 顺序均精确固定；成功 posting 通过既有 generic
  optional packed return 返回单元素 Borsh `FIFOOrderId`，无 posting 仍完全不设置 return data。
  full selected book/eviction、still-crossing remainder、TIF、sequence 异常与未支持 policy 继续
  fail closed。generic Ops/IR/CFG/Component/主 Emit 均未新增 case，持久状态仍只有 account
  bytes、one-based index 与 `0` sentinel，没有 heap Map/Vec、runtime geometry、persistent
  pointer 或无界遍历。当前 digest `d16a4fd2a1a0f648`，assembly 13,696,391 B、ELF
  4,285,024 B、IDL 9,537 B，SHA-256
  `1339e5cd36607b42ad8f2a2f80915f9304ea60d9ea099ca184137f5ef59cdcf7`；229-job Lean、51 个
  SVM build、14 个 EVM build、Phoenix profile 72/72 与 Anvil 14/14 全绿。Surfpool 1.5.0
  以 4,235 个正常 Loader-v3 writes 部署并核对 exact ProgramData，未使用 Test Validator。
  详见 `docs/plan/tasks/l5-056.md`。下一步先在既有 local/`forBody` IR 上补可复用的
  invocation-local bounded scalar fold/frame，再用它组合 multi-maker cursor 与 aggregate fee，
  避免把协议 scratch 写进持久账户或继续扩主 Emit。
- P5 第五十段 invocation-local bounded scalar frame 已完成：抽取器识别 Lean 对两个及以上
  `let mut UInt64` 在静态有界循环中生成的 `MProd`，并直接降到既有
  `letLocal`/`forBody`/`setLocal`；`MProd` 只属 source elaboration，不是 SDK API、runtime
  container 或 target opcode。每次迭代先把所有 next-frame RHS snapshot 到互不重叠的临时
  locals，再统一 publish，因而 swap/相互依赖赋值不会读到前一个写；CPI 等 effect 保持在
  publish 之前。通用 `AccountStorage.Source.read` 可作为 frame scalar，固定 account/word/
  stride/capacity/index-base/access geometry 经 component projection 到 SVM emitter，不复制账户
  或保存 descriptor/pointer。generic Ops/IR/CFG/Component/SVM Emit/EVM Emit 未新增 case；
  persistent state 仍只有 account bytes、fixed stride、one-based index 与 `0` sentinel，没有
  heap Map/Vec、runtime geometry、persistent pointer 或无界遍历。详见
  `docs/plan/tasks/l5-057.md`。下一步用同一 frame 承载 cursor/remaining/quote/fee/stop/error，
  在 `Examples` 组合 bounded multi-maker Limit traversal 与 aggregate settlement。
- P5 第五十一段 bounded two-maker Limit settlement 已完成：`Examples` 中的 Phoenix policy
  先用固定两步只读 traversal + invocation-local scalar frame 预检两个 distinct、non-self、
  no-TIF maker，再以同样的固定两步 traversal replay 原位结算；所有检查在第一条持久写入前
  完成。两笔 maker transition 后只结算一次 taker balance 和 aggregate taker fee，并按
  `Fill(0) → Fill(1) → FillSummary(2)` 生成完整 batch。raw Limit dispatch 继续用旧路径处理
  `matchLimit=1`，用新路径处理 `matchLimit=2`；same-maker aggregation、two-maker remainder、
  TIF、其他 self-trade/soft-funds/remaining-account policy 仍 fail closed。抽取器只修复两个
  sequential scalar frames 间 continuation 的 component effect 保留，未增加 generic Ops、IR、
  CFG、Component、SVM Emit 或 Phoenix-specific emitter vocabulary。持久状态继续只有固定
  account bytes、fixed stride、one-based index 与 `0` sentinel，不使用 heap Map/Vec、runtime
  geometry、detached tree 或 persistent pointer。当前 profile digest `93e5c13d109e21d`，ELF
  4,486,896 B；Phoenix profile Mollusk 74/74。该 exact ELF 已由 Surfpool 1.5.0 经 4,434
  个正常 Loader-v3 writes 部署并成功调用，未使用 Test Validator。详见
  `docs/plan/tasks/l5-058.md`。下一步继续在相同 preflight/replay 组合边界完整覆盖一个
  remainder 或 maker-sequence case，而不是增加底层指令。
- P5 第五十二段 two-maker noncrossing remainder posting 已完成：固定两步只读 preflight
  现在先验证两笔 maker、己方 book capacity/order sequence/duplicate、strict successor
  crossing/TIF、collateral 与 aggregate fee，再执行固定两步 replay；第一条持久写入前已完成
  全部支持性检查。bid remainder 按 taker limit price 锁 quote，ask remainder 锁剩余 base，
  两边都更新 maker/taker balance、unclaimed fee、order/market sequence，并按
  `Fill(0) → Fill(1) → FillSummary(2) → Place(3)` 发 audit；成功 posting 复用 generic
  optional return 返回单元素 `FIFOOrderId`。该切片只组合已有 AccountStorage ordered map/
  one-based allocator、bounded scalar frame、recorder 与 return plan，没有新增 generic Ops、
  IR、CFG、Component 或 Emit case；持久状态仍只有 fixed account bytes/stride/capacity、
  one-based index 与 `0` sentinel，无 heap Map/Vec 或 pointer。当前 digest
  `af159cb894745102`，assembly 14,570,926 B、ELF 4,546,368 B、IDL 9,537 B，SHA-256
  `9cc463b06660fcedf709e8af097eb8302c9ac60a27573b3b7a4163c75427083c`。233-job Lean、
  51 个 SVM build、全 Mollusk 285/285（profile 76/76）、15 个 EVM build 与 Anvil 15/15
  全绿；Surfpool 1.5.0 以 4,493 个正常 Loader-v3 writes 部署并核对 exact
  4,546,413-byte ProgramData，未使用 Test Validator。详见
  `docs/plan/tasks/l5-059.md`。下一切片进入 R0 ownership freeze，不再增加 Phoenix-only
  底层工作。
- R0 ownership freeze 已完成：新增 source API → owner → component → target effect → physical
  state capability matrix，明确共享层只拥有语义值、schema 与 checked control；SVM account
  bytes/index/allocator 与 EVM slot/hashed namespace 分属 target，不建立虚假统一 storage。
  anti-leak checker 与 CI 现在拒绝 `Examples` 直连 target Emit、target 反向 import
  `Examples`/`Projects`，以及 production SVM/EVM 模块出现 Phoenix 协议词；registry 只保留
  artifact enumeration 例外。generic SVM Runtime/storage/FIFO/emitter 文案已去协议化，没有
  修改 Ops、IR、CFG、Component、Runtime 行为或 emitter recipe。IR digest 仍为
  `af159cb894745102`；assembly 因 generic 注释变为 14,572,964 B，ELF 仍为 4,546,368 B、
  IDL 9,537 B、SHA-256
  `9cc463b06660fcedf709e8af097eb8302c9ac60a27573b3b7a4163c75427083c`，与 L5-059 已由
  Surfpool 1.5.0 部署验证的 exact ELF 相同。233-job Lean、51 个 SVM build、Mollusk
  285/285、15 个 EVM build 与 Anvil 15/15 全绿。详见 `docs/plan/tasks/r0-001.md`。下一步
  进入 R1 fixed bytes/u128 logical schema 与 bounded codec plan，不增加协议 recipe opcode。
- EVM contract SDK 第一段已完成：新增 `ProofForge.Evm.Sdk` 作为与 SVM SDK 平行、但不复制
  SVM account geometry 的合同侧 facade。`Address` / `UInt256` / `Bytes32`、`Context`、
  `Immutable`、Ether/Event/Revert、ERC-20/WETH/Uniswap/Permit 统一擦除到既有 target-owned
  runtime/component；`Storage.Layout` 用编译期 cursor 分配 typed U64/address/address-pair 及
  256-bit hashed-map namespace，descriptor 不进入 EVM storage。`Examples.Token` 与
  `Examples.Capped` 已迁移，源代码不再暴露 runtime 名称或 numeric map base；Token/Capped
  canonical digest 仍为 `4da7ac248a0fb556` / `cb058e662f968f65`，target IR 与迁移前逐字节
  相同。该 facade 不包装合同控制流，也未增加 Ops、IR 或 emitter case；SVM 仍使用固定
  account bytes/stride/index，两个 target 只共享 Lean/Profile/Extract/Core CFG。
- P6 第一段 bounded transient heap 模型已完成：按官方 entrypoint allocator 固定
  `0x300000000`、默认 32 KiB / 最大 256 KiB、首 word bump、向下对齐、OOM 与 no-op
  deallocation。它不开放 raw pointer，也不替代账户内 Phoenix/Sokoban allocator。
- `l5-003` 与 Phoenix 双 vault adapter 已完成：Seat 初始化和 Phoenix 同一入口的 canonical PDA 校验、classic SPL Token CPI 成功/失败路径都进 Mollusk。
- `l5-004` Token-2022 classic-compatible program-id 切片已完成；TLV extension 语义仍保持 fail closed。
- `l5-005` 已完成；任务状态已同步为 done。
- P3 横向回归：`lake build Tests`、全 49 个 SVM `pf build`、Mollusk 194/194（含 Phoenix 8/8 与 Tree 2/2）、Anvil 12/12。lowering 修复没有改 Tree digest。

## Phoenix / Solana P0–P5 路线

| 阶段 | 状态 | 依赖 | 验收门 |
|---|---|---|---|
| P0 抽取收口 | 已有 | 通用 Extract state-loop/helper sequencing；SVM CFG/local 布局 | `postAsk` 值树预算、单方法发射、PhoenixSpec、可复现 assembly/ELF/IDL/digest；continuation 不得静默丢 aggregate scalar stores。已知 `postAskFunds` 缺口已关；值树 90,604 / 24,840 是缺口关闭前的探针，本 lowering 后未重测 |
| P1 bounded 产品语义 | 已有 | P0；固定 N=4 账户布局 | ask/bid/trader 三棵持久化树的 N=4 host/IR 门、24 种 topology、双向 IOC、TIF/self-trade/fee/事件与 exact address reuse 全绿 |
| P2 链上认证矩阵 | 已有 | 可组装 Phoenix ELF；classic SPL Token 与 signed self-CPI | Phoenix Mollusk lifecycle/CPI/authenticated audit 矩阵 8/8；跨四档逐样本 chain refinement 补齐前不得宣称 host↔chain 完整 refinement |
| P3 横向回归 | 已有 | P0/P2 产物稳定 | `lake build Tests`、全 SVM `pf build`、SVM Mollusk 194/194、EVM Anvil 12/12 全绿；无 Phoenix 特判。跨四档 host↔chain refinement 仍未宣称；P4 部署资格见下一行 |
| P4 产物资格/压缩 | 已有（本地 Surfpool Loader-v3 transaction；公网未声明） | P0 的稳定 CFG 和可测基线 | 通用 OOB fallthrough + 全图 keyed shared-block；Phoenix assembly 10,642,331 B / ELF 3,429,336 B，digest 不变。ELF 通过 10,485,715 B size gate，并经 Surfpool 1.5.0 的 3,389 write + deploy + authority transactions 落入 exact ProgramData；全 49 SVM + Mollusk 198/198 + Anvil 12/12 回归通过。更深 value-tree CSE 为后续优化 |
| P5 动态 Phoenix-v1 | 部分：profile + complete tree/free-list validation + bounded trader/order insertion/removal + generic component/account-storage boundary + ordered cursor/audit recorder + tag 3 PostOnly/one-maker/two-maker Limit slices + official tags 4–9 + 本地部署门已有 | 固定/固定-stride有界 account region、parent walk、fixed bitmap/stack、effect-safe guarded stores | canonical profile/allocator envelope/三树 invariants 已进 Lean/Mollusk；trader allocator 与 bid/ask books 均可按 Sokoban 0.3.0 填满并逐个删空；word-store、parent path、FIFO/Pubkey RB validators/mutation/key-based cursor 均已迁入 `Component → AccountStorage` bridge；bounded recorder 以 SDK 32 KiB cursor 提供 1,246-byte pre-flush 与 header-only finish；two-word ordered map/one-based allocator source API、zero-remove/nonzero-update policy、Borsh enum variant routing、optional packed return 与 invocation-local bounded scalar frame 已固定，strict PostOnly、one-maker full/partial/remainder posting、two-maker aggregate settlement 与 noncrossing remainder posting、official tags 4–9 均通过 `EntryAdapter + Component` 组合。Phoenix-only 底层切片到此停止，下一步按双目标路线进入 R0 ownership freeze；same-maker aggregation、full-book eviction、remaining accounts 和完整 Phoenix-v1 指令兼容仍 fail closed |
| P6 SDK memory/protocol surface | 进行中：官方形状 transient heap 模型和 recorder lowering 已有 | P5 的 account-resident 边界；后续需要 effect-safe lowering | VM frame 可显式建模 32–256 KiB，但官方 SDK global allocator 固定使用 32 KiB；recorder 遵守同一 cursor/OOM/no-op free。后续只开放 bounded scratch/container API，禁止持久 heap pointer。再分片补 32-byte/u128/Borsh、remaining accounts 和 Token-2022 extension semantics |

P0–P4 不把 Phoenix 名字或字段偏移加入 Extract/IR/emitter。P5 verifier 已能按账户原始
32 bytes 比较 Pubkey，但通用 SDK 的固定长度 32-byte / u128 / Borsh protocol types 仍需
后续设计；现有 contract source 的 Pubkey 与 client id 仍以 `UInt64` limbs 表达。P5 profile
gate 不是把运行时变长账户偷偷放进现有 bounded model，也不是 P0 的验收条件。

Solana Rust 允许 `Vec`/`Box` 等调用期 allocation，但默认 allocator 是有界 bump heap，
不是通用进程 heap；`dealloc` 不回收，pointer 不能跨 invocation 或写入 account。普通
`HashMap` 也不作为 SVM SDK 的默认能力。ProofForge 后续 transient container lowering 必须
携带静态/运行时容量门和显式 OOM，不得把它用于 P5 持久树的全量复制。

## 明确保持 fail closed

- 搬 PF 前端 / `HandlerIR.mk` 私有构造、新 DSL、无约束 Lean、FFI→asm。
- 全 SVM `.so` / loader refinement 与公网部署声明；当前只宣称 Phoenix 本地 Surfpool transaction smoke。
- 运行时 program id、运行时选择的 data offset / 变长 body、运行时 remaining accounts；编译期固定 offset 的 bounds-checked data word 与编译期钉死的 CPI 已开。
- Token-2022 transfer hook / fee / TLV extension 语义，直到对应账户模型落地；当前 base-layout
  wrapper 用精确 data length 在 CPI 前拒绝全部 extension-bearing mint/account。
- feature-gated blake3 / poseidon / curve25519 / alt_bn128 / `sol_get_sysvar`。
- 把完整 32B key 当作现有 8B return-data ABI 的单一返回值。

历史 SDK 清单和阶段分析保留作设计记录，不再当当前 backlog：
[sdk-surface.md](analysis/sdk-surface.md)、[gap-vs-proofforge.md](analysis/gap-vs-proofforge.md)、
[remaining-surface.md](analysis/remaining-surface.md)。
