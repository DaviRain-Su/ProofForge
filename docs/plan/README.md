# 交付计划

分析：[analysis/v0-slice.md](analysis/v0-slice.md) · [analysis/authority.md](analysis/authority.md) · [analysis/gap-vs-proofforge.md](analysis/gap-vs-proofforge.md)

后续权威排期：[Runtime / SDK 双目标路线图](runtime-sdk-roadmap.md)。共享 Lean 语义层，
SVM 与 EVM 各自拥有 Runtime、Component 和物理 storage SDK。
当前边界：[Runtime / SDK capability matrix](capability-matrix.md)。
主流能力基线：[Solana SDK / Solidity + OpenZeppelin parity](mainstream-parity.md)。
多 agent 执行边界：[Runtime / SDK 并行开发执行图](parallel-workstreams.md)。

**当前主线（SVM 全轨）**：[SVM 全面工作计划](svm-work-plan.md)
（能力 Runtime/SDK + 应用 + 语义桥 + 工程 + 形式化）。
形式化子计划：[svm-formalization-plan.md](svm-formalization-plan.md)（`sf-000`…`sf-016`）。
WASM PR #4/#5 继续开着，不阻塞本轨。

任务：

| ID | 状态 | 内容 |
|---|---|---|
| [skel-001](tasks/skel-001.md) | done | Lake 骨架 + Counter 参考语义 |
| [prof-001](tasks/prof-001.md) | done | Profile 传递闭包 |
| [extr-001](tasks/extr-001.md) | done | Expr 抽出 |
| [lowr-001](tasks/lowr-001.md) | done | 本仓 Counter sBPF 发射（对齐 PF StateCell） |
| [asmb-001](tasks/asmb-001.md) | done | sbpf + Mollusk 4/4 |

| [gen-001](tasks/gen-001.md) | done | Expr → checkedAdd 操作序列 |
| [gen-002](tasks/gen-002.md) | done | 按 Op 选择 handler 体 |
| [gen-003](tasks/gen-003.md) | done | 按 Val 生成 load |
| [gen-004](tasks/gen-004.md) | done | 单账户 UInt64 表达式编译器 + decrement |
| [fld-001](tasks/fld-001.md) | done | 多字段 UInt64 布局 + Pair |
| [fld-002](tasks/fld-002.md) | done | 从 structure 收字段 + Pair .so |
| [l1-001](tasks/l1-001.md) | done | 属性入口 + 按名 disc + 多 mutate |
| [l1-002](tasks/l1-002.md) | done | 任意 ite + checked mul/div/mod |
| [l1-003](tasks/l1-003.md) | done | Program 内容寻址 digest |
| [l2-001](tasks/l2-001.md) | done | 带类型字段表 + Option 双叶 |
| [l2-002](tasks/l2-002.md) | done | 定长 Vector UInt64 n |
| [l2-003](tasks/l2-003.md) | done | 本机算出 disc 与 layout marker |
| [l2-004](tasks/l2-004.md) | done | 无 payload 枚举作 tag |
| [l3-001](tasks/l3-001.md) | done | init 写全字段 + view 任意叶子 |
| [l3-002](tasks/l3-002.md) | done | Option match 读 payload |
| [l3-003](tasks/l3-003.md) | done | 单字段用户 inductive 作 tag+payload |
| [l4-001](tasks/l4-001.md) | done | clock.slot + account-0 signer key |
| [l4-002](tasks/l4-002.md) | done | 封闭 system.transfer |
| [evm-001](tasks/evm-001.md) | done | Evm.IR + keccak selector |
| [evm-002](tasks/evm-002.md) | done | Ops → Yul |
| [evm-003](tasks/evm-003.md) | done | `#pf_evm_build` + locked solc |
| [evm-004](tasks/evm-004.md) | done | Anvil ctor / increment / get / overflow |
| [evm-005](tasks/evm-005.md) | done | Pair 多 slot + Anvil |
| [evm-006](tasks/evm-006.md) | done | 窄槽 + Option 双叶 |
| [evm-007](tasks/evm-007.md) | done | Darwin / Linux 共用 Anvil 入口 |
| [evm-008](tasks/evm-008.md) | done | 独立 EVM runtime 叶子 |
| [e-comp-001](tasks/e-comp-001.md) | done | EVM Component 桥：主链路只留一个口 |
| [e-comp-002](tasks/e-comp-002.md) | done | 迁 hashed-map / 256-bit 叶进 Component |
| [e-comp-003](tasks/e-comp-003.md) | done | 迁封闭 CALL 叶进 Component |
| [e-comp-004](tasks/e-comp-004.md) | done | 迁 ETH / LOG / revert / receive 进 Component |
| [e-comp-005](tasks/e-comp-005.md) | done | hashed-map 源侧静态 handle |
| [e-comp-006](tasks/e-comp-006.md) | done | 封闭 CALL / WideWord / NativeFx 源侧 facade |
| [e-comp-007](tasks/e-comp-007.md) | done | Extract 写路径按 Runtime 命名空间收集 |
| [e-comp-008](tasks/e-comp-008.md) | done | Extract 读路径按 Runtime 命名空间收集 |
| [e-comp-009](tasks/e-comp-009.md) | done | WideWord 源侧 limb 查询 |
| [e-comp-010](tasks/e-comp-010.md) | done | HashedMap 源侧 geAddr256 / gePair256 |
| [e-comp-011](tasks/e-comp-011.md) | done | HashedMap 源侧 nextAdd / nextSub |
| [e-comp-012](tasks/e-comp-012.md) | done | HashedMap 源侧 revertInsufficient |
| [e-comp-013](tasks/e-comp-013.md) | done | 地址谓词 isZero20 / eqImm20 |
| [e-pause-001](tasks/e-pause-001.md) | done | Token owner mint + Paused |
| [e-cap-001](tasks/e-cap-001.md) | done | Token mint cap + CapExceeded |
| [e-capped-001](tasks/e-capped-001.md) | done | Capped 复用 owner + pause + cap |
| [e-rt-001](tasks/e-rt-001.md) | done | 环境 + value + Addr20 + ETH + event |
| [e-lang-001](tasks/e-lang-001.md) | done | 位运算 / for / 下标 / ABI / tuple / 命名 revert |
| [e-asset-001](tasks/e-asset-001.md) | done | hashed Map + 封闭 ERC-20 |
| [e-own-001](tasks/e-own-001.md) | done | Ownable + 通用 event + allowance |
| [e-tok-001](tasks/e-tok-001.md) | done | 封闭 ERC-20 形：余额 + 真额度扣减 |
| [l4-003](tasks/l4-003.md) | done | 编译期钉死的 invoke 原语 |
| [l4-004](tasks/l4-004.md) | done | 账户 0 AccountInfo 只读叶子 |
| [l4-005](tasks/l4-005.md) | done | 表层通用 invoke |
| [l4-006](tasks/l4-006.md) | done | findPda 返回 bump |
| [l4-007](tasks/l4-007.md) | done | invokeSigned 一组种子 |
| [l4-008](tasks/l4-008.md) | done | System createAccount |
| [l4-009](tasks/l4-009.md) | done | Token TransferChecked |
| [l4-010](tasks/l4-010.md) | done | ATA CreateIdempotent |
| [l4-011](tasks/l4-011.md) | done | rentExemption |
| [l4-012](tasks/l4-012.md) | done | Token mint / burn |
| [l4-013](tasks/l4-013.md) | done | System assign / allocate |
| [l4-014](tasks/l4-014.md) | done | Token init / close |
| [l4-015](tasks/l4-015.md) | done | Memo write |
| [l4-016](tasks/l4-016.md) | done | createPda |
| [l4-017](tasks/l4-017.md) | done | checkPda |
| [l4-018](tasks/l4-018.md) | done | Token approve / freeze / thaw |
| [l4-019](tasks/l4-019.md) | done | clockEpoch |
| [l4-020](tasks/l4-020.md) | done | Token SetAuthority / Revoke |
| [l4-021](tasks/l4-021.md) | done | slotsPerEpoch |
| [l4-022](tasks/l4-022.md) | done | tokenAccountSize / cpiReturn |
| [l4-023](tasks/l4-023.md) | done | systemAllocateWithSeed |
| [l4-024](tasks/l4-024.md) | done | systemCreateWithSeed |
| [l4-025](tasks/l4-025.md) | done | systemAssignWithSeed |
| [l4-026](tasks/l4-026.md) | done | systemTransferWithSeed |
| [l4-027](tasks/l4-027.md) | done | tokenInitMint |
| [l4-028](tasks/l4-028.md) | done | tokenSyncNative |
| [l4-029](tasks/l4-029.md) | done | 账户 1 只读叶子 |
| [l4-030](tasks/l4-030.md) | done | sha256Lit / sol_sha256 |
| [l4-031](tasks/l4-031.md) | done | 32B key / owner 按字读 |
| [l4-032](tasks/l4-032.md) | done | keccak256Lit / sol_keccak256 |
| [l4-033](tasks/l4-033.md) | done | 账户下标叶子收口 |
| [l4-034](tasks/l4-034.md) | done | 关着的格子一次开完 |
| [l5-001](tasks/l5-001.md) | done | 有界 for 改状态（`fillFirst` 抽出 `forBody`） |
| [l5-002](tasks/l5-002.md) | done | Phoenix bounded N=4 ask lifecycle：挂单 / IOC / self-trade / 结算 |
| [l5-003](tasks/l5-003.md) | done | 席位 PDA + base/quote vault 初始化 + Mollusk 权限门 |
| [l5-004](tasks/l5-004.md) | done | Token-2022 program id 切片 |
| [l5-005](tasks/l5-005.md) | done | 嵌套 structure / Vector element 摊平 + Mollusk |
| [l5-006](tasks/l5-006.md) | done | Sokoban 节点 + allocator/free-list + 完整左右旋 |
| [l5-007](tasks/l5-007.md) | done | Phoenix bounded N=4 bid lifecycle + sell IOC |
| [l5-008](tasks/l5-008.md) | done | Phoenix-v1 canonical owner/header/profile/length gate |
| [l5-009](tasks/l5-009.md) | done | Phoenix-v1 account-resident scalar/allocator-size gate；无 heap/Map |
| [l5-010](tasks/l5-010.md) | done | Phoenix-v1 Sokoban root/bump/free-list header envelope |
| [l5-011](tasks/l5-011.md) | done | Phoenix-v1 bounded account-resident bid-root slot read |
| [l5-012](tasks/l5-012.md) | done | Phoenix-v1 constant-memory bid-root child reciprocity/order gate |
| [l5-013](tasks/l5-013.md) | done | Phoenix-v1 verifier Surfpool Loader-v3 transaction deployment |
| [l5-014](tasks/l5-014.md) | done | Phoenix-v1 bounded parent-path reciprocity/cycle gate |
| [l5-015](tasks/l5-015.md) | done | Phoenix-v1 fixed-memory whole bid tree + allocator partition |
| [l5-016](tasks/l5-016.md) | done | Phoenix-v1 complete ask tree + ascending FIFO ordering |
| [l5-017](tasks/l5-017.md) | done | Phoenix-v1 complete trader tree + 32-byte Pubkey ordering |
| [l5-018](tasks/l5-018.md) | done | Phoenix-v1 bounded account-resident topology-word writes |
| [l5-019](tasks/l5-019.md) | done | Phoenix-v1 exact first trader registration |
| [l5-020](tasks/l5-020.md) | done | Phoenix-v1 exact second trader registration |
| [l5-021](tasks/l5-021.md) | done | Phoenix-v1 exact third trader registration + full insertion fixups |
| [l5-022](tasks/l5-022.md) | done | Phoenix-v1 exact fourth trader registration + red-uncle recolor |
| [l5-023](tasks/l5-023.md) | done | Phoenix-v1 exact fifth trader registration + black-uncle rotations |
| [l5-024](tasks/l5-024.md) | done | Phoenix-v1 general bounded trader insertion |
| [l5-025](tasks/l5-025.md) | done | Phoenix-v1 general bounded trader removal |
| [l5-026](tasks/l5-026.md) | done | Phoenix-v1 fixed-capacity bid/ask insertion |
| [l5-027](tasks/l5-027.md) | done | Phoenix-v1 fixed-capacity bid/ask removal |
| [l5-028](tasks/l5-028.md) | done | Phoenix-v1 fixed-capacity trader get-or-register deposit |
| [l5-029](tasks/l5-029.md) | done | SVM account-resident storage backend boundary + word-store migration |
| [l5-030](tasks/l5-030.md) | done | Bounded account-storage query bridge + parent-path migration |
| [l5-031](tasks/l5-031.md) | done | FIFO RB-tree validator migration + reusable preflight composition |
| [l5-032](tasks/l5-032.md) | done | Pubkey RB-tree validator migration + shared bounded topology |
| [l5-033](tasks/l5-033.md) | done | Bounded account-storage map mutation vocabulary |
| [l5-034](tasks/l5-034.md) | done | Bounded zero/one-based account-storage field reads |
| [l5-035](tasks/l5-035.md) | done | Bounded Key4/FIFO account-storage RB map find |
| [l5-036](tasks/l5-036.md) | done | Source-level bounded RB find + Phoenix validator composition |
| [l5-037](tasks/l5-037.md) | done | Composed Phoenix ReduceOrderWithFreeFunds state transition |
| [l5-038](tasks/l5-038.md) | done | Reusable packed SVM wire/account entry adapter |
| [l5-039](tasks/l5-039.md) | done | Official Phoenix-v1 tag 5 ReduceOrderWithFreeFunds adapter |
| [l5-040](tasks/l5-040.md) | done | Official Phoenix-v1 tag 4 ReduceOrder + Token withdrawal |
| [l5-041](tasks/l5-041.md) | done | Storage-owned scalar-key ordered FIFO cursor |
| [l5-042](tasks/l5-042.md) | done | Stable bounded SVM component bridge |
| [l5-043](tasks/l5-043.md) | done | Bounded invocation-local audit recorder/batching |
| [l5-044](tasks/l5-044.md) | done | Official Phoenix-v1 tags 6/7 CancelAll composition |
| [l5-045](tasks/l5-045.md) | done | Bounded Borsh Option entry plans |
| [l5-046](tasks/l5-046.md) | done | Official Phoenix-v1 tags 8/9 CancelUpTo composition |
| [l5-047](tasks/l5-047.md) | done | Correct Phoenix market/order sequence domains |
| [l5-048](tasks/l5-048.md) | done | Official Phoenix-v1 tag 3 strict PostOnly placement |
| [l5-049](tasks/l5-049.md) | done | Bounded effectful scalar tuple returns |
| [l5-050](tasks/l5-050.md) | done | Phoenix source ownership migration to Examples |
| [l5-051](tasks/l5-051.md) | done | Static account-storage component facade |
| [l5-052](tasks/l5-052.md) | done | Static FIFO cancellation facade |
| [l5-053](tasks/l5-053.md) | done | Static batch-recorder facade |
| [l5-054](tasks/l5-054.md) | done | Reusable ordered storage + one-maker Limit matching |
| [l5-055](tasks/l5-055.md) | done | Consume-in-place storage policy + partial maker fill |
| [l5-056](tasks/l5-056.md) | done | One-maker noncrossing remainder posting |
| [l5-057](tasks/l5-057.md) | done | Invocation-local bounded scalar frames |
| [l5-058](tasks/l5-058.md) | done | Bounded two-maker Limit settlement |
| [l5-059](tasks/l5-059.md) | done | Two-maker noncrossing remainder posting |
| [l6-001](tasks/l6-001.md) | done | Solana 官方形状的 bounded transient bump heap 模型 |
| [r0-001](tasks/r0-001.md) | done | Runtime / SDK ownership matrix 与 anti-leak CI 门 |
| [r1-001](tasks/r1-001.md) | done | Typed codec metadata 与 EVM scalar adapter |
| [r1-002](tasks/r1-002.md) | done | Allocation-free shared boundary values |
| [r1-003](tasks/r1-003.md) | done | Shared scalar SVM Borsh / EVM ABI binding |
| [r1-004](tasks/r1-004.md) | done | Bounded aggregate source schema derivation |
| [r1-005](tasks/r1-005.md) | done | Static record/product/vector SVM Borsh binding |
| [r1-006](tasks/r1-006.md) | done | Canonical tuple/record/fixed-array EVM ABI binding |
| [r1-007](tasks/r1-007.md) | done | Canonical Option/payload-enum SVM Borsh input binding |
| [r1-008](tasks/r1-008.md) | done | EVM Tagged Tuple v1 Option/payload-enum input binding |
| [r1-009](tasks/r1-009.md) | done | SVM fixed-capacity / canonical variable-length Borsh input binding |
| [p-001](tasks/p-001.md) | done | Extract.lean 三段拆分（Lexical / Decode） |
| [p-002](tasks/p-002.md) | done | 第一批 kernel 证明：合约性质定理 |
| [p-003](tasks/p-003.md) | done | asVal 巨石拆分 + Tree 结构不变量证明 |
| [p-004](tasks/p-004.md) | done | removeNode size 守恒 + wf 良构谓词第一批切片 |
| [p-005](tasks/p-005.md) | done | SDK 组件验证：三层策略 + 几何安全定理第一批 |
| [wsm-001](tasks/wsm-001.md) | done | WASM 家族 + XRPL Bedrock 方言 Rust 源 v0 竖切（过渡；产物不是 `.wasm`） |
| [wsm-002](tasks/wsm-002.md) | done | Lean → WAT → `.wasm`；XRPL 拥有 `host_lib` import 与存储布局 |
| [wsm-003](tasks/wsm-003.md) | done | XRPL 本地链工程门：起节点、部署 Counter、四场景 |
| [wsm-005](tasks/wsm-005.md) | done | XRPL-RT：AccountId + caller/self/ledger host 叶子 |
| [wsm-006](tasks/wsm-006.md) | done | XRPL-CMP：三叶 AccountId 比较，unauthorized = 3 |
| [wsm-007](tasks/wsm-007.md) | done | XRPL-HASH：`compute_sha512_half` ASCII 字面量，首个小端 UInt64 |
| [wsm-008](tasks/wsm-008.md) | done | XRPL-SDK：`pf_inline` 转到 Runtime，Ownable 仍是源码 if |
| [wsm-009](tasks/wsm-009.md) | done | XRPL-SDK-EQ：可组合 `AccountId.eq`，Ownable 走 helper |
| [wsm-010](tasks/wsm-010.md) | done | XRPL-SDK-ACCESS：`requireOwner`，Ownable 走门面 |
| [wsm-011](tasks/wsm-011.md) | done | XRPL-RT-2：parent hash 首 u64 + base fee |
| [wsm-012](tasks/wsm-012.md) | done | XRPL-VEC-1：编译期命名槽 `xs_0`…`xs_2` |
| [wsm-013](tasks/wsm-013.md) | done | XRPL-ALPHANET：XLS-0102 host 表 |
| [wsm-014](tasks/wsm-014.md) | done | AlphaNet 零参数烟测 + 本仓 deploy/call |
| [wsm-015](tasks/wsm-015.md) | done | AlphaNet 零参数 Ownable（XrplGate + `pf deploy`/`pf call`） |
| [wsm-016](tasks/wsm-016.md) | done | XRPL-SDK-PAUSE：零参数 Pausable（XrplHold，状态码 4） |
| [wsm-017](tasks/wsm-017.md) | done | XRPL-SDK-MARK：owner 门后写 SHA-512Half（XrplMark） |
| [wsm-018](tasks/wsm-018.md) | planned | 复杂合约缺口排期（[xrpl-next.md](analysis/xrpl-next.md)） |
| [wsm-021](tasks/wsm-021.md) | done | 探针 `trace_num`（AlphaNet 绿；不开 Sdk.Log） |
| [wsm-023](tasks/wsm-023.md) | done | 探针 `cache_le`（import 在；零 id → -10；不开 AccountRoot） |
| [wsm-026](tasks/wsm-026.md) | blocked | 用户 ContractData：caller 可写；合约账户 **-22**；不做 wasm allocator |

## SVM 全面工作计划（当前主线）

总图：[svm-work-plan.md](svm-work-plan.md)。五条轨道并行、写集隔离：

| 轨道 | 任务前缀 | 内容 |
|---|---|---|
| A 形式化 | `sf-*` | L1/L2 kernel 证明收口 → [详案](svm-formalization-plan.md) |
| B Runtime | `svm-rt-*` | signed Clock、Token-2022 extension、alias walk、动态返回… |
| C SDK | `svm-sdk-*` | rent top-up、owner 政策、POD/transient、Memo/migration… |
| D 应用 | `svm-app-*` | Phoenix-v1 指令面、matching/fee、非 Phoenix 例子 |
| E L3 语义 | `svm-sem-*` | sBPF refinement 阶梯 E0–E5（Solanalib + sbpfSemantics） |
| F 工程 | `svm-eng-*` | 形式化 CI 门、双矩阵收口页 |

### Track A — 形式化（`sf-000`…`sf-016`）

| ID | 状态 | 内容 |
|---|---|---|
| [sf-000](tasks/sf-000.md) | todo | 证明基础设施成文 |
| [sf-001](tasks/sf-001.md) | doing | Queue wrap push + 读回（nowrap 已在 main） |
| [sf-002](tasks/sf-002.md) | doing | Queue wrap pop / peek / 往返（clear/advance 已在 main） |
| [sf-003](tasks/sf-003.md) | todo | BoundedVec pop + setAt 读回 |
| [sf-004](tasks/sf-004.md) | todo | Versioned 状态机 |
| [sf-005](tasks/sf-005.md) | todo | StorageBitSet mask 代数 + 账户桥 |
| [sf-006](tasks/sf-006.md) | todo | TransientModel + Vector64 |
| [sf-007](tasks/sf-007.md) | todo | Bytes + Record64 + WideVec |
| [sf-008](tasks/sf-008.md) | todo | Allocator alloc/free 往返 |
| [sf-009](tasks/sf-009.md) | todo | OrderedMap find/insert/remove 模型 |
| [sf-010](tasks/sf-010.md) | todo | StorageEnumerableSet |
| [sf-011](tasks/sf-011.md) | todo | Tree 全树 wf 保持 |
| [sf-012](tasks/sf-012.md) | todo | FifoCancel 有界折料 |
| [sf-013](tasks/sf-013.md) | todo | BatchRecorder begin/append/finish |
| [sf-014](tasks/sf-014.md) | todo | Account / Memory / Sysvar / Telemetry L1 |
| [sf-015](tasks/sf-015.md) | todo | Token / ATA / Pda / System / Memo 扫尾 |
| [sf-016](tasks/sf-016.md) | todo | SVM 形式化收口审计 |

### Track B–F — 能力 / 应用 / 语义 / 工程

| ID | 状态 | 内容 |
|---|---|---|
| [svm-rt-001](tasks/svm-rt-001.md) | todo | Clock signed timestamp |
| [svm-rt-002](tasks/svm-rt-002.md) | todo | Token-2022 第一个 typed extension |
| [svm-rt-003](tasks/svm-rt-003.md) | todo | AccountView+mutation alias-aware walk |
| [svm-rt-004](tasks/svm-rt-004.md) | todo | Instructions / sliced sysvar |
| [svm-rt-005](tasks/svm-rt-005.md) | todo | nested/wide dynamic return 政策 |
| [svm-sdk-001](tasks/svm-sdk-001.md) | todo | resize rent top-up |
| [svm-sdk-002](tasks/svm-sdk-002.md) | todo | owner-reassign 政策 |
| [svm-sdk-003](tasks/svm-sdk-003.md) | todo | generic POD transient shapes |
| [svm-sdk-004](tasks/svm-sdk-004.md) | todo | 更多 manifest-bounded handles |
| [svm-sdk-005](tasks/svm-sdk-005.md) | todo | Token-2022 extension Sdk facade |
| [svm-sdk-006](tasks/svm-sdk-006.md) | todo | UTF-8 Memo + migration payload |
| [svm-sdk-007](tasks/svm-sdk-007.md) | todo | 持久容器有界 iteration |
| [svm-app-001](tasks/svm-app-001.md) | todo | Phoenix-v1 下一组 instruction |
| [svm-app-002](tasks/svm-app-002.md) | todo | matching/fee/remainder 宣称面 |
| [svm-app-003](tasks/svm-app-003.md) | todo | 非 Phoenix SDK 小例子集 |
| [svm-sem-001](tasks/svm-sem-001.md) | todo | L3/E1 operand materialization + straightline |
| [svm-sem-002](tasks/svm-sem-002.md) | todo | L3/E2 assembler-semantics golden 差分门 |
| [svm-sem-003](tasks/svm-sem-003.md) | todo | L3/E3 Counter 整函数 CFG correspondence |
| [svm-sem-004](tasks/svm-sem-004.md) | todo | L3/E4 AccountWords ↔ storev 桥 |
| [svm-sem-005](tasks/svm-sem-005.md) | todo | L3/E5 选定容器全函数有界证明 |
| [svm-eng-001](tasks/svm-eng-001.md) | todo | 形式化门进 CI |
| [svm-eng-002](tasks/svm-eng-002.md) | todo | 能力+证明双矩阵收口页 |

本周默认：`sf-001`（wrap/读回）→`sf-002`（wrap/peek/往返）；并行 `svm-sem-001`；可选 `svm-rt-001`/`svm-sdk-001`；顺手 `svm-eng-001`。
已 merge 当日 main（Queue nowrap/pop 链接 + Core.Math）；WASM PR 仍开着不阻塞。


积压：[backlog.md](backlog.md)
历史 SDK 表面盘点：[analysis/sdk-surface.md](analysis/sdk-surface.md)
XRPL 账本模型 vs EVM/SVM/NEAR：[analysis/xrpl-model.md](analysis/xrpl-model.md)
