# SVM 组件形式化收口计划

> 权威排期：2026-09-01。本文件是 **SVM 形式化轨道（Track A）** 详案。
> SVM 侧能力/应用/语义桥/工程的总图见 **[svm-work-plan.md](svm-work-plan.md)**。
> 继承 [p-005](tasks/p-005.md) 三层策略与 [`ProofForge/Svm/Sdk/StorageModel.lean`](../../ProofForge/Svm/Sdk/StorageModel.lean) 已落地基础。
> WASM 线（PR #4 XRPL / PR #5 NEAR）**保持开着**：本计划不触碰、不阻塞、不合入前提。
> EVM 形式化不在本计划范围。

入口：[SVM 总计划](svm-work-plan.md) · [plan README](README.md) · [capability matrix](capability-matrix.md) · [runtime/SDK roadmap](runtime-sdk-roadmap.md) · [solanalib](../modules/solanalib.md)

---

## 1. 一句话目标

把当前所有 **SVM SDK facade + 其依赖的 target Component 组合逻辑** 在 Lean kernel 下证完：

- **L1**：`wellFormed` / fail-closed 守卫 / 几何与角色下标
- **L2**：在 `AccountWords` 或新建 `TransientWords` 模型上的组合代数

**L3 不在本文件展开**：sBPF correspondence 见总计划 Track E（`svm-sem-*`，E0–E5 要做完；E∞ Agave 主机不承诺）。本文件专注 SDK/Component 的 L1/L2。

「做完」= §6 矩阵每一行 `done` 或显式 `n/a`，且 `scripts/check_no_sorry.py`、`scripts/check_ownership.py`、既有 SVM 工程门全绿。

---

## 2. 信任边界（不可漂移）

| 层 | 验什么 | 怎么验 | 本计划 |
|---|---|---|---|
| L1 描述符 / 守卫 | wellFormed、几何、ASCII bound、role index、pure 谓词 | kernel | **必须做完** |
| L2 组合代数 | 抽象状态上的 RAW、非干涉、push/pop、alloc/free、set 代数 | kernel；模型与 SDK 控制流同构 | **必须做完** |
| 工程门 | `@[irreducible]` 宿主 stub 与发射同语义 | pinned Mollusk / Surfpool | **保持，不扩成证明** |
| L3 refinement | emit ↔ Solanalib/`sbpfSemantics` | 总计划 Track E | **E0–E5 另轨做；本文件不重复** |

禁止「证 stub 占位返回值假装证链上行为」（p-003 负结果）。

---

## 3. 当前基线（开工点）

| 资产 | 位置 | 状态 |
|---|---|---|
| 账户字模型 | `ProofForge/Svm/Sdk/StorageModel.lean` | 字段代数、BoundedVec push、Queue：**empty/nowrap/wrap push 链接+读回**、**pop clear/advance/wrap + 读回**、**peek / initialize / 空往返**（2026-09-01 Phase 1） |
| L1 几何包 | `ProofForge/Svm/Sdk/Storage.lean` | scalarHeader / BoundedVec / RbTree 等一批 wf 定理 |
| Facade L1 切片 | Pubkey / Program / Pda / System / Memo / Token / ATA / OrderedMap 委托 | 有定理但不齐 |
| RB 结构 | `Examples/Tree.lean`（p-003/p-004） | size / 局部 wf；**全树保持未完** |
| Solanalib 桥 | `ProofForge/Svm/Solanalib.lean` | checked arith / branch；与组件代数正交 |

**Queue 收口（Phase 1，2026-09-01）**：

已完成：`mQueuePush_empty_*` / `mQueuePush_nowrap_*` / `mQueuePush_wrap_*`（链接+读回）、
`mQueuePop_clear_*` / `mQueuePop_advance_*` / `mQueuePop_wrap_advance_*`（链接+读回）、
`mQueuePeek_*`、`mQueueInitialize_zero_headers`、`mQueuePush_pop_roundtrip_empty`。

下一形式化刀：SF-2b Versioned（`sf-004`）。
---

## 4. 组件清单

### 4.1 账户持久 SDK → `AccountWords`

| 组件 | 文件 | L1 | L2 | 备注 |
|---|---|---|---|---|
| Field / Region / scalarHeader | `Sdk/Storage.lean` | 部分 done | 字段代数 done | 收成标准引理包 |
| BoundedVec | `Sdk/Storage.lean` | done | push done；**pop/setAt 待补** | 底座 |
| BoundedQueue | `Sdk/Queue.lean` | wf parts done | push/pop 全分支链接+读回、peek、initialize、空往返 **done** | **已收口**；下一刀 Vec |
| BitSet | `Sdk/StorageBitSet.lean` | wf 待定理化 | 单字 mask 代数待建 | 可先纯函数后桥账户 |
| EnumerableSet | `Sdk/StorageEnumerableSet.lean` | wf 待 | 依赖 map + values 槽 | 后置 |
| OrderedMap / RbTree / Allocator | `Sdk/Storage.lean` | 部分委托 done | **模型层几乎空白** | 最大块；对齐 `Examples/Tree.lean` |
| Versioned | `Sdk/Versioned.lean` | wf 待 | classify / initialize / apply | 宜早做 |

### 4.2 薄 facade（几乎只要 L1）

| 组件 | 文件 | 现状 | 收口标准 |
|---|---|---|---|
| Pubkey | `Sdk/Pubkey.lean` | 3 定理 | 等价关系 + word 投影一致 |
| Program.Id | `Sdk/Program.lean` | 2 定理 | canonical id 钉死 + owns 委托 |
| Pda / System seed | `Sdk/Pda.lean` / `Sdk/System.lean` | 部分 | ASCII wf 全覆盖；create* 只证前置 |
| Memo | `Sdk/Memo.lean` | 1 定理 | bound；非特判 writeOk |
| Token | `Sdk/Token.lean` | wf parts | state/tag 守卫完备；CPI 体不进 L2 |
| AssociatedToken | `Sdk/AssociatedToken.lean` | role index | Create + RecoverNested 全 `< L` |
| Account.Handle / View | `Sdk/Account.lean` | **无定理** | wellFormed / word 界 |
| Memory.Span | `Sdk/Memory.lean` | **无定理** | span 几何与非重叠前置 |
| Sysvar / Telemetry | `Sdk/Sysvar.lean` / `Sdk/Telemetry.lean` | **无定理** | L1 API 形状；L2 标 `n/a` |

### 4.3 调用期临时状态 → 新建 `TransientModel`

| 组件 | 文件 | 模型需求 |
|---|---|---|
| HeapBuffer / FixedVec / ByteWriter | `Sdk/Transient.lean` | bump + 两 slot 隔离 |
| Vector64 | `Sdk/TransientVec.lean` | len/cap + push/pop/set |
| Bytes | `Sdk/TransientBytes.lean` | 同上 + appendLe64 |
| Record64 | `Sdk/TransientRecord64.lean` | arity 预检 |
| Vector128 / 256 | `Sdk/TransientWideVec.lean` | 委托 Record64 |

不建模真实堆地址；错误码与 SDK 常量对齐。

### 4.4 Component 组合（不扩 Ops）

| Component | 目录 | 形式化内容 |
|---|---|---|
| AccountStorage | `Svm/AccountStorage/` | Source ≡ 模型字段读写；容器操作落在 SF-1..6 |
| FifoCancel | `Svm/FifoCancel/` | 有界游标步进 + collateral fold |
| BatchRecorder | `Svm/BatchRecorder/` | begin/append/finish 容量与 empty finish |
| Lamports / AccountData | `Svm/Lamports/` · `Svm/AccountData/` | 先 gate 后 store 的顺序定理 |
| AccountView / Memory / Heap | `Svm/AccountView/` · `Memory/` · `Heap/` | 与 Sdk 同几何；Heap 进 TransientModel |
| TransientVec / Bytes | `Svm/TransientVec/` · `TransientBytes/` | effect 序列 ≡ TransientModel |
| Sysvar / Telemetry | `Svm/Sysvar/` · `Telemetry/` | L2 `n/a` |

### 4.5 不在「做完」定义内

Emit / IR / Assembler 正确性、EntryAdapter 全自动 Borsh 证明、Token-2022 全 extension、
Phoenix 撮合正确性、syscall host 全模型、任何 WASM/EVM 工作。

---

## 5. 波次（严格依赖序）

```text
SF-0  证明基础设施（wf-parts / word 引理习惯成文）
  └─► SF-1  Queue 收口                    ← **done**
        └─► SF-2  BoundedVec                     ← 下一刀 pop/set + Versioned
              ├─► SF-3  BitSet
              ├─► SF-4  TransientModel + Vec/Bytes/Record/Wide
              └─► SF-5  Allocator + OrderedMap/Rb
                    ├─► SF-6  EnumerableSet
                    ├─► SF-7  Tree 全树 wf 保持
                    └─► SF-8  FifoCancel + BatchRecorder
                          └─► SF-9  薄 facade / Account / Memory 扫尾
                                └─► SF-10 收口门
```

SF-9 可与 SF-1..4 **并行**（不同文件），但不得改 `StorageModel.lean` 同时抢写。

### 每片验收

1. `lake build` 相关目标绿  
2. 新定理公理集符合仓库标准（通常 `propext` / `Quot.sound`）  
3. `python3 scripts/check_no_sorry.py`  
4. `python3 scripts/check_ownership.py`  

5. 若改 `@[pf_inline]` 控制流：相关 digest / Mollusk 夹具同步  
6. 更新 §6 矩阵 + task front-matter → `done`

---

## 6. 完成矩阵

| ID | 对象 | 层 | 状态 | task |
|---|---|---|---|---|
| SF-0 | wf-parts / word 引理习惯成文 | infra | **done** | [sf-000](tasks/sf-000.md) |
| SF-1a | Queue 非空 push（wrap + 读回） | L2 | **done** | [sf-001](tasks/sf-001.md) |
| SF-1b | Queue pop / peek / initialize / 往返 | L2 | **done** | [sf-002](tasks/sf-002.md) |
| SF-2a | BoundedVec pop + setAt | L2 | **done** | [sf-003](tasks/sf-003.md) |
| SF-2b | Versioned 状态机 | L1+L2 | todo | [sf-004](tasks/sf-004.md) |
| SF-3 | BitSet mask + 账户桥 | L1+L2 | todo | [sf-005](tasks/sf-005.md) |
| SF-4a | TransientModel + Vector64 | L2 | todo | [sf-006](tasks/sf-006.md) |
| SF-4b | Bytes + Record64 + WideVec | L2 | todo | [sf-007](tasks/sf-007.md) |
| SF-5a | Allocator alloc/free 往返 | L2 | todo | [sf-008](tasks/sf-008.md) |
| SF-5b | OrderedMap find/insert/remove | L2 | todo | [sf-009](tasks/sf-009.md) |
| SF-6 | EnumerableSet | L2 | todo | [sf-010](tasks/sf-010.md) |
| SF-7 | Tree 全树 wf 保持 | L2 | todo | [sf-011](tasks/sf-011.md) |
| SF-8a | FifoCancel 有界折料 | L2 | todo | [sf-012](tasks/sf-012.md) |
| SF-8b | BatchRecorder begin/append/finish | L2 | todo | [sf-013](tasks/sf-013.md) |
| SF-9a | Account / Memory / Sysvar / Telemetry L1 | L1 | todo | [sf-014](tasks/sf-014.md) |
| SF-9b | Token / ATA / Pda / System / Memo 扫尾 | L1 | todo | [sf-015](tasks/sf-015.md) |
| SF-10 | 收口审计 | gate | todo | [sf-016](tasks/sf-016.md) |

---

## 7. 实施约定

1. **词级引理优先**：`mWriteWord_self` / `mWriteWord_other` 串联；少展开 `UInt64` `ite`（见 p-005 记录）。
2. **wf 先拆 parts**：统一 `*_wf_parts`，禁止脆弱深投影。
3. **模型 ≅ SDK 控制流**：同守卫、同写序；不同构先改模型。
4. **持久 vs 临时分文件**：持久继续 `StorageModel.lean`（可拆子模块）；临时新建 `TransientModel.lean`。
5. **禁止**为证明去改 Emit / Ops / IR 主路径；SDK 只允许证明友好的等价抽出。
6. **单 PR 粒度**：一个操作族（如「Queue pop 全行为」），2–6 个定理。

---

## 8. 与既有文档关系

- Runtime/SDK 能力切片已实现；本计划是 **形式化债务清零**，不新开 Runtime 能力。
- capability matrix 的 Available 不变；本计划把 Available 升级为 **Available + kernel L1/L2**。
- backlog 继续记工程证据；形式化进度以 **§6 矩阵** 为准。
- p-001..p-005 保持历史 done；新片只用 **`sf-*`**。

---

## 9. 开工 checklist

1. 读 §2 §7 与 [p-005](tasks/p-005.md)  
2. [sf-000](tasks/sf-000.md) → **done**  
3. [sf-001](tasks/sf-001.md) / [sf-002](tasks/sf-002.md) → **done**（Queue 收口）  
4. 下一刀 [sf-003](tasks/sf-003.md)（Vec pop/setAt），按波次向下，每片更新矩阵  
5. [sf-016](tasks/sf-016.md) 收口  

WASM PR #4 / #5：继续开着；本轨不要求它们先合。
外分支对 SVM 的真实重叠仅 `Svm/IR` reject 臂 / EntryAdapter 拒 foreign annotation / README 任务表——见 [svm-work-plan.md §3.2](svm-work-plan.md)；**不改** L3 阶梯。