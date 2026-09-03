# SVM 全面工作计划

> 权威排期：2026-09-01。本文是 **Solana/SVM 侧接下来要做完的全部工作** 总图，
> 不只形式化。形式化子计划见 [svm-formalization-plan.md](svm-formalization-plan.md)。
>
> 继承：[runtime-sdk-roadmap.md](runtime-sdk-roadmap.md) · [mainstream-parity.md](mainstream-parity.md) ·
> [capability-matrix.md](capability-matrix.md) · [backlog.md](backlog.md)
>
> **不做 / 另轨**：EVM 能力切片；WASM PR #4 / #5（保持开着、不阻塞）。
> **L3（sBPF refinement）要做，但是阶梯式**：见 Track E；不做的是「一次性 Agave 全主机
> 语义 + ELF/loader 全程序闭环」这种无限天花板宣称。

---

## 1. 一句话

把 SVM 从「能力切片大多已落地 + 证明刚起步」推到：

1. **能力**：R2/R3 剩余缺口按主流 parity F0–F2 收完（仍 fail-closed）  
2. **证明**：SDK/Component L1+L2 形式化收口（`sf-*`）  
3. **应用**：Phoenix-v1 指令/撮合策略补到可宣称的协议面  
4. **L3 语义桥**：用已接入的 `solanalib` + `sbpfSemantics`（assembler-semantics）把
   emit 片段 → 可执行 sBPF 语义的 correspondence **按阶梯做完到 Counter/容器级**  
5. **工程门**：CI / digest / Mollusk / Surfpool 稳定可重复

「做完」不是复制整个 Solana SDK crate，也不是一夜证完 Agave；而是 roadmap §2 的
**v1 ceiling** + 下面 §2.1 的 L3 阶梯终点。

---

## 2. 六条轨道（可并行，但有锁）

```text
┌─────────────────────────────────────────────────────────────┐
│ Track A  Formalization     sf-000 … sf-016   （SDK L1/L2）  │
│ Track B  Runtime gaps      svm-rt-*          （R2 剩余）    │
│ Track C  SDK gaps          svm-sdk-*         （R3 / F1–F2） │
│ Track D  Application       svm-app-*         （Phoenix-v1） │
│ Track E  L3 semantics      svm-sem-*         （sBPF 桥）    │
│ Track F  Engineering       svm-eng-*         （CI / 门禁）  │
└─────────────────────────────────────────────────────────────┘
```

| 轨道 | 写什么 | 不写什么 | 与谁并行 |
|---|---|---|---|
| A 形式化 | `StorageModel` / `TransientModel` / `Examples/Tree` 定理 | Emit/Ops 主路径 | 可与 B/C 并行（**不同文件**） |
| B Runtime | `Svm` Runtime/Component/sysvar/CPI/Token-2022 TLV 语义 | Phoenix 业务名 | 改 Component 时锁 A 的同文件模型 |
| C SDK | `Svm.Sdk` facade / 容器 / lifecycle | 协议策略 | 新容器落地后 **立刻** 挂 A 的 L1/L2 任务 |
| D 应用 | `Examples.Svm.Phoenix*` 指令与 matching | Runtime leaf / recipe opcode | 只组合已有 SDK |
| E L3 语义 | Solanalib / `sbpfSemantics` fragment→program ladder | Agave 全主机/ELF 闭环宣称 | 与 A 互补；先吃稳定 emit 形状 |
| F 工程 | CI lane、manifest、文档索引 | 产品语义 | 任意时刻可插 |

### 2.1 Track E：L3 为什么「可以做」，以及做到哪

已接入依赖：

- `solanalib`（Solana Foundation `leanprover-solanalib`）— typed sBPF 指令 + small-step  
- `sbpfSemantics`（`assembler-semantics` @ `64770b7`）— `.s` → L2 语义 / golden pipeline  

**已有基线（不是从零）**：`ProofForge/Svm/Solanalib.lean` 已有 checked arith body/guard、
static store、CFG write handoff、六种 unsigned branch 的 correspondence；
`SemanticsBridge.lean` 已有 `.s` → L2 解析与步进入口。

L3 在本计划里定义为 **阶梯**，不是二元「做/不做」：

| 阶 | 内容 | 终点判据 | 状态 |
|---|---|---|---|
| E0 | 单指令 / 短 fragment ↔ Solanalib `step` | 已有 arith/store/branch | **已有** |
| E1 | operand materialization + 多指令 straightline | **done**（Counter field/arg/lit → straightline） | `svm-sem-001` |
| E2 | `.s` golden ↔ `sbpfSemantics` 解析/步进 | **done**（Counter+Window + named parse） | `svm-sem-002` |
| E3 | 整函数 CFG（有界 block）end-to-end correspondence | **done**（Counter increment 三块 CFG） | `svm-sem-003` |
| E4 | 账户字模型（Track A）与 sBPF 内存 store 的桥 | **done**（Counter value word ↔ storev/loadv） | `svm-sem-004` |
| E5 | 多入口程序 / 简单容器例（Queue push 空路径） | **done**（Queue empty-push L3） | `svm-sem-005` |
| E∞ | Loader-v3 + syscall/CPI/sysvar 主机 + ELF 接受 | Agave 忠实全程序 | **不承诺为本轨完成条件** |

**E0–E5 要规划、要做完。** E∞ 留作远景：缺主机模型就无法诚实声称；不挡 E0–E5 收口。E∞ 刀族已于 2026-09-02 停在 `svm-sem-140`（第 135 刀，account-19 skip；PR #24 account-19 field arc 已关闭），替代方向是一条对 account 数量与 data 长度参数化的 skip-chain 引理。

**硬规则（来自 ownership freeze）**

- 新能力先判：SDK 组合 → Component → 真缺的底层 effect；只有最后一种才扩 Ops/IR/Emit。  
- SVM 持久态禁止 native pointer / 跨 invocation heap。  
- Phoenix 名字、offset、撮合策略不得进入 `ProofForge/Svm`。  
- 每个能力切片至少两个非 Phoenix consumer（已有惯例继续）。

---

## 3. 现状快照（2026-09-01，已合并当日 main）

| 面 | 已有 | 主要剩余 |
|---|---|---|
| Runtime (R2) | remaining-account view、scratch/CPI plan、signer tail、Token-2022 TLV envelope、program-memory、telemetry、Clock/EpochSchedule/Rent unsigned、checked lamports、resize | **signed Clock**、**Instructions/sliced sysvar**、**AccountView+direct mutation 的 alias-aware variable walk**、**nested/wide dynamic return**、**Token-2022 各 extension 完整语义** |
| SDK (R3) | Account/Signer/PDA/System/Token/ATA/Memo、POD 容器全家桶、version header、transient 双 slot、wide vectors、close/refund、**rent top-up**、Token-2022 mint-close facade；**owner-reassign = n/a fail-closed** | **runtime-selected ATA/Memo geometry**、**UTF-8 Memo**、**richer POD migrate shapes**、**更多 manifesto slot + insert/remove/iter**、**更多 Token-2022 extension** |
| Shared math（新） | `Core.Math.UInt64` + `Core.FixedPoint.UInt64` + SafeCast→UInt8/16；SVM Mollusk `core_math` + EVM Anvil 双 consumer（R1-024…031 / R5-022/023） | signed / 更宽 root·sat / typed fixed-point — **不挡 SVM 主线**；Phoenix fee 可直接组合 |
| 形式化 (A) | SF-0..SF-10 **done**（Queue/Vec/BitSet/Transient/Alloc/Map/Set/Tree几何/FifoCancel/BatchRecorder/facade L1） | 可选加厚（Tree 可达/互逆）；L3 见 Track E |
| 应用 | Phoenix N=4 + Phoenix-v1 profile（部分 instruction）；新增 `BatchSizer`（吃 Core.Math） | **CancelUpTo 之后的指令面**、matching/fee（现可直接用 mulDiv/FixedPoint）、跨 target conformance |
| 语义桥 / L3 | checked arith / CFG branch correspondence；assembler-semantics golden（E0） | E1–E5 ladder |
| 工程 | 三 lane CI、Lean/SVM/EVM 门 | 形式化门进 CI、artifact/digest 漂移说明 |
| WASM（外分支） | PR #4 XRPL / PR #5 NEAR 仍开、持续推进 | **不并入本轨、不阻塞**；合入时只做窄缝适配（§3.2） |

### 3.1 相对本计划起草点的 delta（main 已吸收）

| 来源 | 变更 | 对本轨影响 |
|---|---|---|
| **Phase 1–7 Track A** | SF-0..SF-10 形式化收口 | **全部 done**（sf-016）；勿重证 Queue nowrap/pop 已落定理；下一主刀 Track B `svm-rt-*` |
| **main** R1-024…031 | shared UInt64 math + fixed-point | Track D fee/matching **少造轮子**；不新增 Runtime leaf |
| **main** R5-022/023 | SafeCast→UInt8/16 | 共享层；非 blocker |
| **main** docs | backlog / roadmap / capability / parity 刷新 | 本分支已 merge；总图入口保留 |

本计划分支已 **merge 当日 `origin/main`**（与 `origin/main` 无 ahead commits）。后续开工以合并后树为准；再拉 main 只防新 Queue/math 提交。

### 3.2 外分支快照与对本轨影响（2026-09-01 复核）

| 分支 / PR | 相对 main | 实质内容 | 碰到的 SVM/共享面 | 对本轨 |
|---|---|---|---|---|
| **main** | = 本计划 merge-base | Queue 证明 + Core.Math（已吃） | `StorageModel` / `Core.*` | **已吸收**；Phase 1 勿重做 |
| **wasm-near** #5 | ~10 commits behind main；持续 force-push 风格推进 | NEAR FT / storage deposit·unregister / JSON / Promise 竖切 | `Svm/IR.lean`（reject `.near`）、`Svm/EntryAdapter.lean`（拒 foreign annotation）、`Tests/SvmSdkPubkeySpec.lean`、大量 `docs/plan/README` wsm 行 | **能力正交**；合入时机械补 exhaustiveness，**不改** StorageModel / L3 / Phoenix |
| **wasm-feature** #4 | ~86 commits behind main | XRPL Bedrock 能力长尾（escrow/lock/trustline 探针等） | `Svm/IR.lean`（reject `.xrpl`）、`docs/plan/README` wsm 行 | 同上；比 near 更旧，合入冲突主要在 **文档表** |

**窄缝详情（合入 WASM 时必做，平时不做）**

1. `Extract.IR.ValKind` / `OpExt` 一旦出现 `.xrpl` / `.near`，`ProofForge/Svm/IR.lean` 的 `projectValExt` / `projectOpExt` / `projectionError` 必须补 reject 臂（外分支已有补丁形状可抄）。  
2. `EntryAdapter.decode` 若合入 near 的「拒非 `svm.raw.*` annotation」策略，与本轨 Runtime/SDK 工作不冲突，合并时保留即可。  
3. `docs/plan/README.md` 任务表会大面积冲突：以 **保留本轨 `sf-*` / `svm-*` 入口 + 并入 wsm 行** 为策略，勿让 WASM 表冲掉 SVM 计划链接。  
4. NEAR `Queue64` / XRPL 容器与 SVM `StorageModel` Queue **无共享实现**；概念对标可参考，**禁止**为对齐 WASM 去改 SVM 证明目标。

**规划结论（不改 Phase 顺序）**

- Phase 1–7 **不变**；外分支不插入新 Phase。  
- 本轨实现 PR **禁止**以 `wasm-near` / `wasm-feature` 为 base。  
- 若 WASM 先合 main：本轨下一次 `merge origin/main` 时只做 §3.2 窄缝 + README 表合并，然后继续 sf-002。  
- 若本轨证明先合：WASM 合入时由他们补 reject 臂（他们分支上已有）。

---

## 4. 推荐总序（给人排期用）

不必严格串行；下列是 **依赖友好** 的默认顺序。括号内是并行建议。

```text
Phase 0   导航对齐
          · 读本文 + formalization-plan + mainstream-parity §4–5
          · 确认 WASM PR 不阻塞

Phase 1   证明主线（吃 main 余量）+ L3 阶梯启动 + Runtime 小缺口   ← 立刻
          · A: sf-000..sf-011 几何 **done** → **sf-012 FifoCancel / sf-013 BatchRecorder**（done）
            （empty/nowrap/wrap push 链接+读回、pop clear/advance/wrap 已完成，禁止重做）
          · E: svm-sem-001 operand materialization / straightline（**done**）
          · B: svm-rt-001 signed Clock（可并行）
          · F: svm-eng-001 形式化 CI 门（**done**）
          · D 侧注：fee/matching 直接组合 `Core.Math` / `FixedPoint`，勿再开共享算术片

Phase 2   持久容器证明 + SDK lifecycle + L3 golden 门
          · A: sf-003..sf-005（Vec / Versioned / BitSet）
          · E: svm-sem-002 assembler-semantics corpus 差分门（**done**）
          · C: svm-sdk-001..007 + svm-rt-004/`005` + svm-sem-001..`005` + svm-app-001/`002` **done** → next: Tracks A–F closeout audit
          · C: svm-sdk-002 **done (n/a)** owner-reassign 永久 fail-closed
          · C: svm-sdk-004 **done** ResourceManifest 先行；live >2 仍 fail-closed
          · F: svm-eng-002 **done** (status matrix + `scripts/svm_status_summary.py`)
          · E: svm-sem-001 **done** (Counter field/arg/lit materialize + straightline)

Phase 3   Transient 证明 + SDK 形状加宽 + Counter 全函数 L3
          · A: sf-006..sf-007（TransientModel）
          · E: svm-sem-003 Counter increment 有界 CFG end-to-end **done**
          · E: svm-sem-004 AccountWords ↔ typed storev 桥 **done**
          · C: svm-sdk-003 generic POD transient record shapes（**done**）
          · C: svm-sdk-004 更多 manifest-bounded transient slots（**done**：manifest-first）

Phase 4   Map/Tree 证明 + Token-2022 + 内存桥
          · A: sf-008..sf-011（Allocator/Map/EnumerableSet/Tree）
          · B/C: svm-rt-002 + svm-sdk-005 Token-2022 第一批 extension
                （已选 `MintCloseAuthority`；双 consumer + fail-closed 已落地）

Phase 5   Component 组合证明 + Phoenix 指令面 + 容器 L3
          · A: sf-012..sf-013（FifoCancel / BatchRecorder）
          · E: svm-sem-005 Queue empty-push L3 **done**
          · D: svm-app-001 Phoenix-v1 下一指令族（**done**：tags 10/11 CancelMultipleById cap=4）
          · D: svm-app-002 matching/fee/remainder 宣称面 **done**（tag 3 有界片）
          · D: svm-app-003 非 Phoenix SDK 小例子集 **done**

Phase 6   Facade 扫尾 + 序列化/返回政策
          · A: sf-014..sf-015
          · B: svm-rt-005 nested/wide dynamic return **done**（`ReturnBudget`；digest `243ea72de353e8e3`）
          · C: svm-sdk-006 UTF-8 Memo / richer migration payload（**done**）

Phase 7   收口
          · A: sf-016 形式化审计
          · E: E0–E5 看板全绿（E∞ 可仍为远景 n/a）
          · F: svm-eng-002 SVM 能力+证明+L3 三矩阵声明 **done**
          · D: svm-app-003 非 Phoenix 例子集（若未并行完成）
```

---

## 5. 轨道明细与任务 ID

### Track A — 形式化（已有完整切片）

权威：[svm-formalization-plan.md](svm-formalization-plan.md)  
任务：`sf-000` … `sf-016`  
完成定义：该文 §6 矩阵全 `done` / `n/a`。

### Track B — Runtime 剩余

| ID | 内容 | 优先级 | 验收 |
|---|---|---|---|
| [svm-rt-001](tasks/svm-rt-001.md) | Clock **signed** timestamp 视图（与 unsigned 字段并存；明确布局） | F1 | **done**；Lean + Mollusk 12/12；digest `19039a4899e65b6d` |
| [svm-rt-002](tasks/svm-rt-002.md) | Token-2022 **第一个** typed extension：`MintCloseAuthority`（非 transfer-fee） | F2 | **done**；CPI `Token2022MintClose` + Sdk host parse；fee/hook/未知仍 fail-closed；digest `607b3786fb54eaee` |
| [svm-rt-003](tasks/svm-rt-003.md) | AccountView 与 direct mutation 共用时的 **alias-aware** 变量 walk | F1 | **done**；`AccountViewMutation` digest `fee09f06d0cc60d4`；Mollusk 6/6；view-only digest 不变 |
| [svm-rt-004](tasks/svm-rt-004.md) | Instructions / sliced sysvar（有界） | F2 | **done**；digest `fa750f0ebf227df3` |
| [svm-rt-005](tasks/svm-rt-005.md) | nested / constructed / wide dynamic **return** 政策（仍有界） | F0/F1 | **done** — `ReturnBudget`; tags 27/29; Mollusk wide U128 |

### Track C — SDK 剩余

| ID | 内容 | 优先级 | 验收 |
|---|---|---|---|
| [svm-sdk-001](tasks/svm-sdk-001.md) | resize **rent top-up** 显式政策（组合 Rent sysvar + lamports） | F1 | **done**；`topUpRentExempt`/`resizeDataWithRentTopUp`；digests `389be3285e53c93d` / `754ab90d0d3145ae`；Mollusk 4+2 |
| [svm-sdk-002](tasks/svm-sdk-002.md) | **owner-reassign** 生命周期（或书面永久 fail-closed + 矩阵 n/a） | F1 | **done (n/a)**；永久 fail-closed；Lean policy guard + Mollusk foreign-owner reject |
| [svm-sdk-003](tasks/svm-sdk-003.md) | generic POD transient shapes（超出 Record64/Vector128/256 的下一形状） | F1 | **done**；`VectorPubkey`；digests `8958053c8b1f52ac` / `106f41e98d4dcc9c`；Mollusk 8/8 |
| [svm-sdk-004](tasks/svm-sdk-004.md) | 更多 manifest-bounded transient **handles**（>2 需 resource manifest） | F1 | **done**；`ResourceManifest` 先行；默认 2；`>2` fail-closed 至 scratch relayout |
| [svm-sdk-005](tasks/svm-sdk-005.md) | Token-2022 extension 的 **Sdk facade**（对接 rt-002） | F2 | **done**；`Sdk.Token2022` mint-close view/CPI；不把 extension 名写进 Emit |
| [svm-sdk-006](tasks/svm-sdk-006.md) | UTF-8 Memo + richer account **migration payload** shapes | F1/F2 | **done**；`Memo.Utf8` ≤512 + `PayloadTransition` 单边；digests `c13eb931ded2755a` / `39327e5abe0c9299`；Mollusk 2+5 |
| [svm-sdk-007](tasks/svm-sdk-007.md) | 持久容器 insert/remove/**iteration** 有界 API（在现有 Map/Set 上） | F1/F2 | **done**；`valueAt`/`removeAt`/`clear` + Queue `getAt`；digests `22c051a109d012b5` / `6857a73c4f999356` / `11b8e19a66200ed7`；Mollusk 7+3 |

> 新 SDK 容器一落地，就在 Track A 追加对应 `sf-*`（或扩展现有片），避免「能跑无证」堆积。

### Track D — 应用（Phoenix 等）

| ID | 内容 | 验收 |
|---|---|---|
| [svm-app-001](tasks/svm-app-001.md) | Phoenix-v1 下一组官方 instruction 组合（只扩 Examples） | **done**；tags 10/11 CancelMultipleById（cap=8；见 app-004/005/007）；digest `72e24d00aee1781c`；CancelById Mollusk 含八 id |
| [svm-app-002](tasks/svm-app-002.md) | matching / fee / remainder 策略缺口补到文档宣称面 | **done** — tag 3 matching/fee/remainder |
| [svm-app-004](tasks/svm-app-004.md) | Phoenix CancelMultipleById Vec capacity 1→2 | **done** — maxDataLen 39; Mollusk dual-id |
| [svm-app-005](tasks/svm-app-005.md) | Phoenix CancelMultipleById Vec capacity 2→4 | **done** — maxDataLen 73; Mollusk four-id |
| [svm-app-006](tasks/svm-app-006.md) | Phoenix CancelMultipleById tag-10 four-id withdraw | **done** — Mollusk aggregate quote claim |
| [svm-app-007](tasks/svm-app-007.md) | Phoenix CancelMultipleById tag-11 capacity 4→8 | **done** — tag11 maxDataLen 141 |
| [svm-app-008](tasks/svm-app-008.md) | Phoenix CancelMultipleById tag-10 capacity 4→5 | **done** — maxDataLen 90; digest `5fddbc7822acef7e` |
| [svm-app-009](tasks/svm-app-009.md) | Phoenix CancelMultipleById tag-10 capacity 5→6 | **done** — seam 1088; maxDataLen 107; digest `b88c8a2247d2c28e` |
| [svm-app-010](tasks/svm-app-010.md) | Phoenix CancelMultipleById tag-10 capacity 6→7 | **done** — seam 1152; maxDataLen 124; digest `31c33408a7d9dbf7` |
| [svm-app-011](tasks/svm-app-011.md) | Phoenix CancelMultipleById tag-10 capacity 7→8 | **done** — seam 1216; maxDataLen 141; digest `6bf08db0730bf300` |
| [svm-app-012](tasks/svm-app-012.md) | Phoenix WithdrawFunds tag 12 (exact-lots) | **done** — wire 17; digest `c67cc383aa680001` |
| [svm-app-013](tasks/svm-app-013.md) | Phoenix DepositFunds tag 13 (exact-lots) | **done** — wire 17; digest `5e9097d41f7cefbf` (at land) |
| [svm-app-014](tasks/svm-app-014.md) | Phoenix WithdrawFunds tag 12 (`Option<u64>` withdraw-all) | **done** — digest `f248b89dc0fb8def`; Mollusk Option matrix |
| [svm-app-015](tasks/svm-app-015.md) | Phoenix DepositFunds tag 13 (`Option<u64>` deposit-all) | **done** — digest `1049b9843a832a95`; Mollusk Option matrix |
| [svm-app-016](tasks/svm-app-016.md) | Phoenix RequestSeat tag 14 | **done** — seat PDA create + Approved record + trader-tree insert; digest `c50584a88d34bf4b` |
| [svm-app-003](tasks/svm-app-003.md) | 非 Phoenix 小例子：Queue/Map/BitSet/Versioned 各一（证明 SDK 可复用） | **done** — TicketLine/FeatureBits/UniqueRoster/VersionedLedger + Mollusk |

### Track E — L3 sBPF 语义桥（阶梯 E0–E5）

依赖：已 pin 的 `solanalib` + `sbpfSemantics`（assembler-semantics）。E0 已有基线。

| ID | 阶 | 内容 | 验收 |
|---|---|---|---|
| （基线） | E0 | checked arith / store / branch fragment ↔ Solanalib `step` | **已有** |
| [svm-sem-001](tasks/svm-sem-001.md) | E1 | operand materialization + 多指令 straightline | **done** — Counter field/arg/lit → straightline; axioms `propext`/`Quot.sound`/`native_decide` |
| [svm-sem-002](tasks/svm-sem-002.md) | E2 | `.s` golden ↔ `sbpfSemantics` 解析/步进差分门 | **done** — Counter+Window；named parse；`Tests.SemanticsSpec` |
| [svm-sem-003](tasks/svm-sem-003.md) | E3 | 整函数有界 CFG end-to-end（Counter increment） | **done** — 三块 CFG；7+5/max+1；≤3 blocks/≤64 instr |
| [svm-sem-004](tasks/svm-sem-004.md) | E4 | Track A `AccountWords` ↔ typed `storev` 内存桥 | **done** — Counter value word；roundtrip/OOB/`evalStaticStore` |
| [svm-sem-005](tasks/svm-sem-005.md) | E5 | 选定容器例全函数（Queue empty-push） | **done** — TicketLine 布局；三写 storev 投影 |
| [svm-sem-006](tasks/svm-sem-006.md) | E∞ knife | walked `r7` arg cursor ↔ E1 absolute `.arg` | **done** — first host knife |
| [svm-sem-007](tasks/svm-sem-007.md) | E∞ knife 2 | two consecutive walked `r7` u64 args ↔ E1 | **done** — multi-field cursor |
| [svm-sem-008](tasks/svm-sem-008.md) | E∞ knife 3 | Loader account-0 header/key walk ↔ abs load | **done** — non-dup + key limb |
| [svm-sem-009](tasks/svm-sem-009.md) | E∞ knife 4 | Loader account-0 signer/writable flags ↔ abs load | **done** — Emit gate bytes |
| [svm-sem-010](tasks/svm-sem-010.md) | E∞ knife 5 | Loader account-0 lamports/data_len ↔ abs load | **done** — Emit budget words |
| [svm-sem-011](tasks/svm-sem-011.md) | E∞ knife 6 | Loader account-0 owner limbs 0/1 ↔ abs load | **done** — Emit ACC0_OWNER words |
| [svm-sem-012](tasks/svm-sem-012.md) | E∞ knife 7 | Loader account-0 owner limbs 2/3 ↔ abs load | **done** — Emit ACC0_OWNER+16/+24 |
| [svm-sem-013](tasks/svm-sem-013.md) | E∞ knife | Loader account-0 executable + rent_epoch | **done** — knife 8; zero-dataLen rent at `0x2860` |
| [svm-sem-014](tasks/svm-sem-014.md) | E∞ knife | Loader account-0 → next-account marker | **done** — knife 9; skip to `0x2868` |
| [svm-sem-015](tasks/svm-sem-015.md) | E∞ knife | Loader account-1 header/key after skip | **done** — knife 10; `0x2868`/`0x2870` |
| [svm-sem-016](tasks/svm-sem-016.md) | E∞ knife | Loader account-1 signer/writable after skip | **done** — knife 11; `0x2869`/`0x286a` |
| [svm-sem-017](tasks/svm-sem-017.md) | E∞ knife | Loader account-1 lamports/data_len after skip | **done** — knife 12; header+0x48/+0x50 |
| [svm-sem-018](tasks/svm-sem-018.md) | E∞ knife | Loader account-1 owner limbs 0/1 after skip | **done** — knife 13; header+0x28/+0x30 |
| [svm-sem-019](tasks/svm-sem-019.md) | E∞ knife | Loader account-1 owner limbs 2/3 after skip | **done** — knife 14; header+0x38/+0x40 |
| [svm-sem-020](tasks/svm-sem-020.md) | E∞ knife | Loader account-1 executable/rent after skip | **done** — knife 15; header+3/+0x2858 |
| [svm-sem-021](tasks/svm-sem-021.md) | E∞ knife | Loader account-1 → account-2 skip chain | **done** — knife 16; chained emitSkipAccount |
| [svm-sem-022](tasks/svm-sem-022.md) | E∞ knife | Loader account-2 header/key after skip chain | **done** — knife 17; acc2 header/key |
| [svm-sem-023](tasks/svm-sem-023.md) | E∞ knife | Loader account-2 signer/writable after skip chain | **done** — knife 18; header+1/+2 |
| [svm-sem-024](tasks/svm-sem-024.md) | E∞ knife | Loader account-2 lamports/data_len after skip chain | **done** — knife 19; header+0x48/+0x50 |
| [svm-sem-025](tasks/svm-sem-025.md) | E∞ knife | Loader account-2 owner limbs 0/1 after skip chain | **done** — knife 20; header+0x28/+0x30 |
| [svm-sem-026](tasks/svm-sem-026.md) | E∞ knife | Loader account-2 owner limbs 2/3 after skip chain | **done** — knife 21; header+0x38/+0x40 |
| [svm-sem-027](tasks/svm-sem-027.md) | E∞ knife | Loader account-2 executable/rent after skip chain | **done** — knife 22; header+3/+0x2858 |
| [svm-sem-028](tasks/svm-sem-028.md) | E∞ knife | Loader account-2 → account-3 skip chain | **done** — knife 23; triple emitSkipAccount |
| [svm-sem-029](tasks/svm-sem-029.md) | E∞ knife | Loader account-3 header/key after skip chain | **done** — knife 24; acc3 header/key |
| [svm-sem-030](tasks/svm-sem-030.md) | E∞ knife | Loader account-3 signer/writable after skip chain | **done** — knife 25; header+1/+2 |
| [svm-sem-031](tasks/svm-sem-031.md) | E∞ knife | Loader account-3 lamports/data_len after skip chain | **done** — knife 26; header+0x48/+0x50 |
| [svm-sem-032](tasks/svm-sem-032.md) | E∞ knife | Loader account-3 owner limbs 0/1 after skip chain | **done** — knife 27; header+0x28/+0x30 |
| [svm-sem-033](tasks/svm-sem-033.md) | E∞ knife | Loader account-3 owner limbs 2/3 after skip chain | **done** — knife 28; header+0x38/+0x40 |
| [svm-sem-034](tasks/svm-sem-034.md) | E∞ knife | Loader account-3 executable/rent after skip chain | **done** — knife 29; header+3/+0x2858 |
| [svm-sem-035](tasks/svm-sem-035.md) | E∞ knife | Loader account-3 → account-4 skip chain | **done** — knife 30; quadruple emitSkipAccount |
| [svm-sem-036](tasks/svm-sem-036.md) | E∞ knife | Loader account-4 header/key after skip chain | **done** — knife 31; acc4 header/key |
| [svm-sem-037](tasks/svm-sem-037.md) | E∞ knife | Loader account-4 signer/writable after skip chain | **done** — knife 32; acc4 flags |
| [svm-sem-038](tasks/svm-sem-038.md) | E∞ knife | Loader account-4 lamports/data_len after skip chain | **done** — knife 33; acc4 budget |
| [svm-sem-039](tasks/svm-sem-039.md) | E∞ knife | Loader account-4 owner limbs 0/1 after skip chain | **done** — knife 34; acc4 owner lo |
| [svm-sem-040](tasks/svm-sem-040.md) | E∞ knife | Loader account-4 owner limbs 2/3 after skip chain | **done** — knife 35; acc4 owner hi |
| [svm-sem-041](tasks/svm-sem-041.md) | E∞ knife | Loader account-4 executable/rent after skip chain | **done** — knife 36; acc4 exec/rent |
| [svm-sem-042](tasks/svm-sem-042.md) | E∞ knife | Loader account-4 → account-5 skip chain | **done** — knife 37; acc5 skip |
| [svm-sem-043](tasks/svm-sem-043.md) | E∞ knife | Loader account-5 header/key after skip chain | **done** — knife 38; acc5 header/key |
| [svm-sem-044](tasks/svm-sem-044.md) | E∞ knife | Loader account-5 signer/writable after skip chain | **done** — knife 39; acc5 flags |
| [svm-sem-045](tasks/svm-sem-045.md) | E∞ knife | Loader account-5 lamports/data_len after skip chain | **done** — knife 40; acc5 budget |
| [svm-sem-046](tasks/svm-sem-046.md) | E∞ knife | Loader account-5 owner limbs 0/1 after skip chain | **done** — knife 41; acc5 owner lo |
| [svm-sem-047](tasks/svm-sem-047.md) | E∞ knife | Loader account-5 owner limbs 2/3 after skip chain | **done** — knife 42; acc5 owner hi |
| [svm-sem-048](tasks/svm-sem-048.md) | E∞ knife | Loader account-5 executable/rent after skip chain | **done** — knife 43; acc5 exec/rent |
| [svm-sem-049](tasks/svm-sem-049.md) | E∞ knife | Loader account-5 → account-6 skip chain | **done** — knife 44; acc6 skip |
| [svm-sem-050](tasks/svm-sem-050.md) | E∞ knife | Loader account-6 header/key after skip chain | **done** — knife 45; acc6 header/key |
| [svm-sem-051](tasks/svm-sem-051.md) | E∞ knife | Loader account-6 signer/writable after skip chain | **done** — knife 46; acc6 flags |
| [svm-sem-052](tasks/svm-sem-052.md) | E∞ knife | Loader account-6 lamports/data_len after skip chain | **done** — knife 47; acc6 budget |
| [svm-sem-053](tasks/svm-sem-053.md) | E∞ knife | Loader account-6 owner limbs 0/1 after skip chain | **done** — knife 48; acc6 owner lo |
| [svm-sem-054](tasks/svm-sem-054.md) | E∞ knife | Loader account-6 owner limbs 2/3 after skip chain | **done** — knife 49; acc6 owner hi |
| [svm-sem-055](tasks/svm-sem-055.md) | E∞ knife | Loader account-6 executable/rent after skip chain | **done** — knife 50; acc6 exec/rent |
| [svm-sem-056](tasks/svm-sem-056.md) | E∞ knife | Loader account-6 → account-7 skip chain | **done** — knife 51; acc7 skip |
| [svm-sem-057](tasks/svm-sem-057.md) | E∞ knife | Loader account-7 header/key after skip chain | **done** — knife 52; acc7 header/key |
| [svm-sem-058](tasks/svm-sem-058.md) | E∞ knife | Loader account-7 signer/writable after skip chain | **done** — knife 53; acc7 flags |
| [svm-sem-059](tasks/svm-sem-059.md) | E∞ knife | Loader account-7 lamports/data_len after skip chain | **done** — knife 54; acc7 budget |
| [svm-sem-060](tasks/svm-sem-060.md) | E∞ knife | Loader account-7 owner limbs 0/1 after skip chain | **done** — knife 55; acc7 owner lo |
| [svm-sem-061](tasks/svm-sem-061.md) | E∞ knife | Loader account-7 owner limbs 2/3 after skip chain | **done** — knife 56; acc7 owner hi |
| [svm-sem-062](tasks/svm-sem-062.md) | E∞ knife | Loader account-7 executable/rent after skip chain | **done** — knife 57; acc7 exec/rent |
| [svm-sem-063](tasks/svm-sem-063.md) | E∞ knife | Loader account-7 → account-8 skip chain | **done** — knife 58; acc8 skip |
| [svm-sem-064](tasks/svm-sem-064.md) | E∞ knife | Loader account-8 header/key after skip chain | **done** — knife 59; acc8 header/key |
| [svm-sem-065](tasks/svm-sem-065.md) | E∞ knife | Loader account-8 signer/writable after skip chain | **done** — knife 60; acc8 flags |
| [svm-sem-066](tasks/svm-sem-066.md) | E∞ knife | Loader account-8 lamports/data_len after skip chain | **done** — knife 61; acc8 budget |
| [svm-sem-067](tasks/svm-sem-067.md) | E∞ knife | Loader account-8 owner limbs 0/1 after skip chain | **done** — knife 62; acc8 owner lo |
| [svm-sem-068](tasks/svm-sem-068.md) | E∞ knife | Loader account-8 owner limbs 2/3 after skip chain | **done** — knife 63; acc8 owner hi |
| [svm-sem-069](tasks/svm-sem-069.md) | E∞ knife | Loader account-8 executable/rent after skip chain | **done** — knife 64; acc8 exec/rent |
| [svm-sem-070](tasks/svm-sem-070.md) | E∞ knife | Loader account-8 → account-9 skip chain | **done** — knife 65; acc9 skip |
| [svm-sem-071](tasks/svm-sem-071.md) | E∞ knife | Loader account-9 header/key after skip chain | **done** — knife 66; acc9 header/key |
| [svm-sem-072](tasks/svm-sem-072.md) | E∞ knife | Loader account-9 signer/writable after skip chain | **done** — knife 67; acc9 flags |
| [svm-sem-073](tasks/svm-sem-073.md) | E∞ knife | Loader account-9 lamports/data_len after skip chain | **done** — knife 68; acc9 budget |
| [svm-sem-074](tasks/svm-sem-074.md) | E∞ knife | Loader account-9 owner limbs 0/1 after skip chain | **done** — knife 69; acc9 owner lo |
| [svm-sem-075](tasks/svm-sem-075.md) | E∞ knife | Loader account-9 owner limbs 2/3 after skip chain | **done** — knife 70; acc9 owner hi |
| [svm-sem-076](tasks/svm-sem-076.md) | E∞ knife | Loader account-9 executable/rent after skip chain | **done** — knife 71; acc9 exec/rent |
| [svm-sem-077](tasks/svm-sem-077.md) | E∞ knife | Loader account-9 → account-10 skip chain | **done** — knife 72; acc10 skip |
| [svm-sem-078](tasks/svm-sem-078.md) | E∞ knife | Loader account-10 header/key after skip chain | **done** — knife 73; acc10 header/key |
| [svm-sem-079](tasks/svm-sem-079.md) | E∞ knife | Loader account-10 signer/writable after skip chain | **done** — knife 74; acc10 flags |
| [svm-sem-080](tasks/svm-sem-080.md) | E∞ knife | Loader account-10 lamports/data_len after skip chain | **done** — knife 75; acc10 budget |
| [svm-sem-081](tasks/svm-sem-081.md) | E∞ knife | Loader account-10 owner limbs 0/1 after skip chain | **done** — knife 76; acc10 owner lo |
| [svm-sem-082](tasks/svm-sem-082.md) | E∞ knife | Loader account-10 owner limbs 2/3 after skip chain | **done** — knife 77; acc10 owner hi |
| [svm-sem-083](tasks/svm-sem-083.md) | E∞ knife | Loader account-10 executable/rent after skip chain | **done** — knife 78; acc10 exec/rent |
| [svm-sem-084](tasks/svm-sem-084.md) | E∞ knife | Loader account-10 → account-11 skip chain | **done** — knife 79; acc11 skip |
| [svm-sem-085](tasks/svm-sem-085.md) | E∞ knife | Loader account-11 header/key after skip chain | **done** — knife 80; acc11 header/key |
| [svm-sem-086](tasks/svm-sem-086.md) | E∞ knife | Loader account-11 signer/writable after skip chain | **done** — knife 81; acc11 flags |
| [svm-sem-087](tasks/svm-sem-087.md) | E∞ knife | Loader account-11 lamports/data_len after skip chain | **done** — knife 82; acc11 budget |
| [svm-sem-088](tasks/svm-sem-088.md) | E∞ knife | Loader account-11 owner limbs 0/1 after skip chain | **done** — knife 83; acc11 owner lo |
| [svm-sem-089](tasks/svm-sem-089.md) | E∞ knife | Loader account-11 owner limbs 2/3 after skip chain | **done** — knife 84; acc11 owner hi |
| [svm-sem-090](tasks/svm-sem-090.md) | E∞ knife | Loader account-11 executable/rent after skip chain | **done** — knife 85; acc11 exec/rent |
| [svm-sem-091](tasks/svm-sem-091.md) | E∞ knife | Loader account-11 → account-12 skip chain | **done** — knife 86; acc12 skip |
| [svm-sem-092](tasks/svm-sem-092.md) | E∞ knife | Loader account-12 header/key after skip chain | **done** — knife 87; acc12 header/key |
| [svm-sem-093](tasks/svm-sem-093.md) | E∞ knife | Loader account-12 signer/writable after skip chain | **done** — knife 88; acc12 flags |
| [svm-sem-094](tasks/svm-sem-094.md) | E∞ knife | Loader account-12 lamports/data_len after skip chain | **done** — knife 89; acc12 budget |
| [svm-sem-095](tasks/svm-sem-095.md) | E∞ knife | Loader account-12 owner limbs 0/1 after skip chain | **done** — knife 90; acc12 owner lo |
| [svm-sem-096](tasks/svm-sem-096.md) | E∞ knife | Loader account-12 owner limbs 2/3 after skip chain | **done** — knife 91; acc12 owner hi |
| [svm-sem-097](tasks/svm-sem-097.md) | E∞ knife | Loader account-12 executable/rent after skip chain | **done** — knife 92; acc12 exec/rent |
| [svm-sem-098](tasks/svm-sem-098.md) | E∞ knife | Loader account-12 → account-13 skip chain | **done** — knife 93; acc13 skip |
| [svm-sem-099](tasks/svm-sem-099.md) | E∞ knife | Loader account-13 header/key after skip chain | **done** — knife 94; acc13 header/key |
| [svm-sem-100](tasks/svm-sem-100.md) | E∞ knife | Loader account-13 signer/writable after skip chain | **done** — knife 95; acc13 flags |
| [svm-sem-101](tasks/svm-sem-101.md) | E∞ knife | Loader account-13 lamports/data_len after skip chain | **done** — knife 96; acc13 budget |
| [svm-sem-102](tasks/svm-sem-102.md) | E∞ knife | Loader account-13 owner limbs 0/1 after skip chain | **done** — knife 97; acc13 owner lo |
| [svm-sem-103](tasks/svm-sem-103.md) | E∞ knife | Loader account-13 owner limbs 2/3 after skip chain | **done** — knife 98; acc13 owner hi |
| [svm-sem-104](tasks/svm-sem-104.md) | E∞ knife | Loader account-13 executable/rent after skip chain | **done** — knife 99; acc13 exec/rent |
| [svm-sem-105](tasks/svm-sem-105.md) | E∞ knife | Loader account-13 → account-14 skip chain | **done** — knife 100; acc14 skip |
| [svm-sem-106](tasks/svm-sem-106.md) | E∞ knife | Loader account-14 header/key after skip chain | **done** — knife 101; acc14 header/key |
| [svm-sem-107](tasks/svm-sem-107.md) | E∞ knife | Loader account-14 signer/writable after skip chain | **done** — knife 102; acc14 flags |
| [svm-sem-108](tasks/svm-sem-108.md) | E∞ knife | Loader account-14 lamports/data_len after skip chain | **done** — knife 103; acc14 budget |
| [svm-sem-109](tasks/svm-sem-109.md) | E∞ knife | Loader account-14 owner limbs 0/1 after skip chain | **done** — knife 104; acc14 owner lo |
| [svm-sem-110](tasks/svm-sem-110.md) | E∞ knife | Loader account-14 owner limbs 2/3 after skip chain | **done** — knife 105; acc14 owner hi |
| [svm-sem-111](tasks/svm-sem-111.md) | E∞ knife | Loader account-14 executable/rent after skip chain | **done** — knife 106; acc14 exec/rent |
| [svm-sem-112](tasks/svm-sem-112.md) | E∞ knife | Loader account-14 → account-15 skip chain | **done** — knife 107; acc15 skip |
| [svm-sem-113](tasks/svm-sem-113.md) | E∞ knife | Loader account-15 header/key after skip chain | **done** — knife 108; acc15 header/key |
| [svm-sem-114](tasks/svm-sem-114.md) | E∞ knife | Loader account-15 signer/writable after skip chain | **done** — knife 109; acc15 flags |
| [svm-sem-115](tasks/svm-sem-115.md) | E∞ knife | Loader account-15 lamports/data_len after skip chain | **done** — knife 110; acc15 budget |
| [svm-sem-116](tasks/svm-sem-116.md) | E∞ knife | Loader account-15 owner limbs 0/1 after skip chain | **done** — knife 111; acc15 owner lo |
| [svm-sem-117](tasks/svm-sem-117.md) | E∞ knife | Loader account-15 owner limbs 2/3 after skip chain | **done** — knife 112; acc15 owner hi |
| [svm-sem-118](tasks/svm-sem-118.md) | E∞ knife | Loader account-15 executable/rent after skip chain | **done** — knife 113; acc15 exec/rent |
| [svm-sem-119](tasks/svm-sem-119.md) | E∞ knife | Loader account-15 → account-16 skip chain | **done** — knife 114; acc16 skip |
| [svm-sem-120](tasks/svm-sem-120.md) | E∞ knife | Loader account-16 header/key after skip chain | **done** — knife 115; acc16 header/key |
| [svm-sem-121](tasks/svm-sem-121.md) | E∞ knife | Loader account-16 signer/writable after skip chain | **done** — knife 116; acc16 flags |
| [svm-sem-122](tasks/svm-sem-122.md) | E∞ knife | Loader account-16 lamports/data_len after skip chain | **done** — knife 117; acc16 budget |
| [svm-sem-123](tasks/svm-sem-123.md) | E∞ knife | Loader account-16 owner limbs 0/1 after skip chain | **done** — knife 118; acc16 owner lo |
| [svm-sem-124](tasks/svm-sem-124.md) | E∞ knife | Loader account-16 owner limbs 2/3 after skip chain | **done** — knife 119; acc16 owner hi |
| [svm-sem-125](tasks/svm-sem-125.md) | E∞ knife | Loader account-16 executable/rent after skip chain | **done** — knife 120; acc16 exec/rent |
| [svm-sem-126](tasks/svm-sem-126.md) | E∞ knife | Loader account-16 → account-17 skip chain | **done** — knife 121; acc17 skip |
| [svm-sem-127](tasks/svm-sem-127.md) | E∞ knife | Loader account-17 header/key after skip chain | **done** — knife 122; acc17 header/key |
| [svm-sem-128](tasks/svm-sem-128.md) | E∞ knife | Loader account-17 signer/writable after skip chain | **done** — knife 123; acc17 flags |
| [svm-sem-129](tasks/svm-sem-129.md) | E∞ knife | Loader account-17 lamports/data_len after skip chain | **done** — knife 124; acc17 budget |
| [svm-sem-130](tasks/svm-sem-130.md) | E∞ knife | Loader account-17 owner limbs 0/1 after skip chain | **done** — knife 125; acc17 owner lo |
| [svm-sem-131](tasks/svm-sem-131.md) | E∞ knife | Loader account-17 owner limbs 2/3 after skip chain | **done** — knife 126; acc17 owner hi |
| [svm-sem-132](tasks/svm-sem-132.md) | E∞ knife | Loader account-17 executable/rent after skip chain | **done** — knife 127; acc17 exec/rent |
| [svm-sem-133](tasks/svm-sem-133.md) | E∞ knife | Loader account-17 → account-18 skip chain | **done** — knife 128; acc18 skip |
| [svm-sem-134](tasks/svm-sem-134.md) | E∞ knife | Loader account-18 header/key after skip chain | **done** — knife 129; acc18 header/key |
| [svm-sem-135](tasks/svm-sem-135.md) | E∞ knife | Loader account-18 signer/writable after skip chain | **done** — knife 130; acc18 flags |
| [svm-sem-136](tasks/svm-sem-136.md) | E∞ knife | Loader account-18 lamports/data_len after skip chain | **done** — knife 131; acc18 budget |
| [svm-sem-137](tasks/svm-sem-137.md) | E∞ knife | Loader account-18 owner limbs 0/1 after skip chain | **done** — knife 132; acc18 owner lo |
| [svm-sem-138](tasks/svm-sem-138.md) | E∞ knife | Loader account-18 owner limbs 2/3 after skip chain | **done** — knife 133; acc18 owner hi |
| [svm-sem-139](tasks/svm-sem-139.md) | E∞ knife | Loader account-18 executable/rent after skip chain | **done** — knife 134; acc18 exec/rent |
| [svm-sem-140](tasks/svm-sem-140.md) | E∞ knife | Loader account-18 → account-19 skip chain | **done** — knife 135; acc19 skip |
| — | E∞ | Loader-v3 + syscall/CPI/sysvar 主机 + ELF 接受 | **远景**；非本轨完成条件 |

### Track F — 工程

| ID | 内容 | 验收 |
|---|---|---|
| [svm-eng-001](tasks/svm-eng-001.md) | CI：`check_no_sorry` + 形式化相关 lake 目标进 SVM/Lean lane | **done**；Lean 具名 Proof/Solanalib/Semantics；SVM 同步 ownership+no-sorry |
| [svm-eng-002](tasks/svm-eng-002.md) | 双矩阵收口：能力矩阵 + 形式化矩阵同一声明页 | **done** — [svm-status-matrix.md](svm-status-matrix.md) + summary script |

---

## 6. 总看板

状态：`todo` / `doing` / `done` / `n/a`

| 轨道 | 片 | 状态 |
|---|---|---|
| A | sf-000 … sf-016 | **全部 done**（SF-7 几何 done；可达/互逆可选加厚） |
| B | svm-rt-001 … 005 | **全部 done**（005 digest `243ea72de353e8e3`） |
| C | svm-sdk-001 … 007 | **全部 done**（002 = n/a fail-closed；004 = manifest-first, >2 fail-closed） |
| D | svm-app-001 … 003 | **001 done**；002/003 todo（fee 可依赖已合入的 Core.Math） |
| E | svm-sem-001 … 005（E0 已有） | svm-sem-001/`002`/`003` **done**；004–005 todo |
| F | svm-eng-001 … 002 | **全部 done**（[svm-status-matrix.md](svm-status-matrix.md)） |

---

## 7. 与旧文档的关系

| 文档 | 关系 |
|---|---|
| `runtime-sdk-roadmap.md` | 双目标权威能力排期；本文 **只展开 SVM 剩余 + 证明 + 应用** |
| `mainstream-parity.md` | F0–F3 定义；本文 Track B/C 的优先级来源 |
| `svm-formalization-plan.md` | Track A 详案；本文不重复定理清单 |
| `backlog.md` | 工程证据流水；进度看板以本文 §6 + 形式化 §6 为准 |
| `parallel-workstreams.md` | 多 agent 写集；开并行前先对表 |

---

## 8. 明确不做 / 远景（写清，避免范围漂移）

**本轨不做或不作为完成条件：**

- EVM Runtime/SDK 切片（另用 R4/R5）  
- WASM / XRPL / NEAR（PR 保持开）  
- **E∞**：Agave 忠实的 Loader-v3 + 全 syscall/CPI/sysvar 主机 + ELF 接受闭环  
  （缺主机模型；不挡 E0–E5）  
- 无界 `Array` / account 内 `HashMap` / 跨调用 heap  
- 未单开的 Token-2022 extension 静默兼容  
- 把 Phoenix 策略下沉进 SDK/Emit  

**本轨要做完：** Track E 的 **E0–E5**（有界 fragment → Counter/容器级 correspondence）。 

---

## 9. 开工建议（本周）

1. **主线能力**：through `svm-rt-005` + SDK + eng + **`svm-sem-001`..`005`** + **`svm-app-001`..`003`** done → Tracks A–F closeout audit **done**（`tasks/svm-closeout-audit.md`）
2. **WASM**：PR #4/#5 继续开着；本轨不跟 `wasm-near` 抢写

能力片合并时：若引入新 SDK 表面，同步开/扩对应 `sf-*`。
状态板：[`svm-status-matrix.md`](svm-status-matrix.md) / `python3 scripts/svm_status_summary.py`。
