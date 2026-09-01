# SVM 全面工作计划

> 权威排期：2026-09-01。本文是 **Solana/SVM 侧接下来要做完的全部工作** 总图，
> 不只形式化。形式化子计划见 [svm-formalization-plan.md](svm-formalization-plan.md)。
>
> 继承：[runtime-sdk-roadmap.md](runtime-sdk-roadmap.md) · [mainstream-parity.md](mainstream-parity.md) ·
> [capability-matrix.md](capability-matrix.md) · [backlog.md](backlog.md)
>
> **不做 / 另轨**：EVM 能力切片；WASM PR #4 / #5（保持开着、不阻塞）；sBPF L3 refinement。

---

## 1. 一句话

把 SVM 从「能力切片大多已落地 + 证明刚起步」推到：

1. **能力**：R2/R3 剩余缺口按主流 parity F0–F2 收完（仍 fail-closed）  
2. **证明**：SDK/Component L1+L2 形式化收口（`sf-*`）  
3. **应用**：Phoenix-v1 指令/撮合策略补到可宣称的协议面  
4. **语义桥**：Solanalib / assembler-semantics 覆盖面按需加深  
5. **工程门**：CI / digest / Mollusk / Surfpool 稳定可重复

「做完」不是复制整个 Solana SDK crate，而是 roadmap §2 的 **v1 ceiling**：定宽、有界、显式 effect；未建模能力稳定拒绝。

---

## 2. 五条轨道（可并行，但有锁）

```text
┌─────────────────────────────────────────────────────────────┐
│ Track A  Formalization     sf-000 … sf-016                  │
│ Track B  Runtime gaps      svm-rt-*   （R2 剩余）            │
│ Track C  SDK gaps          svm-sdk-*  （R3 剩余 / F1–F2）    │
│ Track D  Application       svm-app-*  （Phoenix-v1 等）      │
│ Track E  Semantics bridge  svm-sem-*  （Solanalib 加深）     │
│ Track F  Engineering       svm-eng-*  （CI / 文档 / 门禁）   │
└─────────────────────────────────────────────────────────────┘
```

| 轨道 | 写什么 | 不写什么 | 与谁并行 |
|---|---|---|---|
| A 形式化 | `StorageModel` / `TransientModel` / `Examples/Tree` 定理 | Emit/Ops 主路径 | 可与 B/C 并行（**不同文件**） |
| B Runtime | `Svm` Runtime/Component/sysvar/CPI/Token-2022 TLV 语义 | Phoenix 业务名 | 改 Component 时锁 A 的同文件模型 |
| C SDK | `Svm.Sdk` facade / 容器 / lifecycle | 协议策略 | 新容器落地后 **立刻** 挂 A 的 L1/L2 任务 |
| D 应用 | `Examples.Phoenix*` 指令与 matching | Runtime leaf / recipe opcode | 只组合已有 SDK |
| E 语义桥 | Solanalib correspondence 扩面 | 全程序 refinement | 不挡 A–D |
| F 工程 | CI lane、manifest、文档索引 | 产品语义 | 任意时刻可插 |

**硬规则（来自 ownership freeze）**

- 新能力先判：SDK 组合 → Component → 真缺的底层 effect；只有最后一种才扩 Ops/IR/Emit。  
- SVM 持久态禁止 native pointer / 跨 invocation heap。  
- Phoenix 名字、offset、撮合策略不得进入 `ProofForge/Svm`。  
- 每个能力切片至少两个非 Phoenix consumer（已有惯例继续）。

---

## 3. 现状快照（2026-09-01）

| 面 | 已有 | 主要剩余 |
|---|---|---|
| Runtime (R2) | remaining-account view、scratch/CPI plan、signer tail、Token-2022 TLV envelope、program-memory、telemetry、Clock/EpochSchedule/Rent unsigned、checked lamports、resize | **signed Clock**、**Instructions/sliced sysvar**、**AccountView+direct mutation 的 alias-aware variable walk**、**nested/wide dynamic return**、**Token-2022 各 extension 完整语义** |
| SDK (R3) | Account/Signer/PDA/System/Token/ATA/Memo、POD 容器全家桶、version header、transient 双 slot、wide vectors、close/refund | **rent top-up / owner-reassign**、**runtime-selected ATA/Memo geometry**、**UTF-8 Memo**、**richer POD migrate shapes**、**更多 manifest slot + insert/remove/iter**、**Token-2022 extension facade** |
| 形式化 (A) | StorageModel、Queue 空 push 读回、一批 L1 facade、Tree 局部 | 见 `sf-*`：Queue 收口 → Vec/BitSet/Map/Transient/Tree/Component |
| 应用 | Phoenix N=4 + Phoenix-v1 profile（部分 instruction） | **CancelUpTo 之后的指令面**、matching/fee 策略补全、跨 target conformance example |
| 语义桥 | checked arith / CFG branch correspondence；assembler-semantics golden | operand materialization、更大 fragment、与 StorageModel 对齐的信任叙述 |
| 工程 | 三 lane CI、406 Lean jobs、67 SVM / Mollusk 全绿 | 形式化门进 CI、artifact/digest 漂移说明、计划矩阵自动化可选 |

---

## 4. 推荐总序（给人排期用）

不必严格串行；下列是 **依赖友好** 的默认顺序。括号内是并行建议。

```text
Phase 0   导航对齐
          · 读本文 + formalization-plan + mainstream-parity §4–5
          · 确认 WASM PR 不阻塞

Phase 1   证明主线启动 + Runtime 小缺口   ← 立刻
          · A: sf-000 → sf-001 → sf-002（Queue 收口）
          · B: svm-rt-001 signed Clock（可并行）
          · F: svm-eng-001 形式化 CI 门（可并行）

Phase 2   持久容器证明 + SDK lifecycle
          · A: sf-003..sf-005（Vec / Versioned / BitSet）
          · C: svm-sdk-001 rent top-up + close 政策收口
          · C: svm-sdk-002 owner-reassign 显式政策（fail-closed 边界写清）

Phase 3   Transient 证明 + SDK 形状加宽
          · A: sf-006..sf-007（TransientModel）
          · C: svm-sdk-003 generic POD transient record shapes
          · C: svm-sdk-004 更多 manifest-bounded transient slots

Phase 4   Map/Tree 证明 + Token-2022
          · A: sf-008..sf-011（Allocator/Map/EnumerableSet/Tree）
          · B/C: svm-rt-002 + svm-sdk-005 Token-2022 第一批 extension
                （transfer-fee 或 mint-close-authority，选一个有双 consumer 的）

Phase 5   Component 组合证明 + Phoenix 指令面
          · A: sf-012..sf-013（FifoCancel / BatchRecorder）
          · D: svm-app-001 Phoenix-v1 下一指令族（在现有 SDK 上组合）
          · D: svm-app-002 matching/fee 缺口补片（仍只在 Examples）

Phase 6   Facade 扫尾 + 序列化/返回政策
          · A: sf-014..sf-015
          · B: svm-rt-003 nested/wide dynamic return（若仍在 ceiling 内）
          · C: svm-sdk-006 UTF-8 Memo / richer migration payload

Phase 7   收口
          · A: sf-016 形式化审计
          · F: svm-eng-002 SVM 能力+证明双矩阵全绿声明
          · E: svm-sem-001 按需加深（不挡收口）
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
| [svm-rt-001](tasks/svm-rt-001.md) | Clock **signed** timestamp 视图（与 unsigned 字段并存；明确布局） | F1 | Lean + Mollusk；错误布局 fail closed |
| [svm-rt-002](tasks/svm-rt-002.md) | Token-2022 **第一个** typed extension 语义（建议 transfer-fee **或** mint-close-authority） | F2 | 双 consumer；未知 extension 仍原子拒绝 |
| [svm-rt-003](tasks/svm-rt-003.md) | AccountView 与 direct mutation 共用时的 **alias-aware** 变量 walk | F1 | 别名/只读/owner 矩阵；无 persistent pointer |
| [svm-rt-004](tasks/svm-rt-004.md) | Instructions / sliced sysvar（有界） | F2 | 按需；无通用任意切片 |
| [svm-rt-005](tasks/svm-rt-005.md) | nested / constructed / wide dynamic **return** 政策（仍有界） | F0/F1 | 与 codec budget 一致；超界 fail closed |

### Track C — SDK 剩余

| ID | 内容 | 优先级 | 验收 |
|---|---|---|---|
| [svm-sdk-001](tasks/svm-sdk-001.md) | resize **rent top-up** 显式政策（组合 Rent sysvar + lamports） | F1 | 两 consumer；不足租金 fail closed |
| [svm-sdk-002](tasks/svm-sdk-002.md) | **owner-reassign** 生命周期（或书面永久 fail-closed + 矩阵 n/a） | F1 | 政策二选一，禁止半开 |
| [svm-sdk-003](tasks/svm-sdk-003.md) | generic POD transient shapes（超出 Record64/Vector128/256 的下一形状） | F1 | 同 slot 生命周期复用；双 consumer |
| [svm-sdk-004](tasks/svm-sdk-004.md) | 更多 manifest-bounded transient **handles**（>2 需 resource manifest） | F1 | manifest 先行；默认仍 2 |
| [svm-sdk-005](tasks/svm-sdk-005.md) | Token-2022 extension 的 **Sdk facade**（对接 rt-002） | F2 | 不把 extension 名写进 Emit |
| [svm-sdk-006](tasks/svm-sdk-006.md) | UTF-8 Memo + richer account **migration payload** shapes | F1/F2 | strict UTF-8；migration 单边显式 |
| [svm-sdk-007](tasks/svm-sdk-007.md) | 持久容器 insert/remove/**iteration** 有界 API（在现有 Map/Set 上） | F1/F2 | 无 heap iterator object |

> 新 SDK 容器一落地，就在 Track A 追加对应 `sf-*`（或扩展现有片），避免「能跑无证」堆积。

### Track D — 应用（Phoenix 等）

| ID | 内容 | 验收 |
|---|---|---|
| [svm-app-001](tasks/svm-app-001.md) | Phoenix-v1 下一组官方 instruction 组合（只扩 Examples） | Mollusk；digest 纪律；无新 Ops |
| [svm-app-002](tasks/svm-app-002.md) | matching / fee / remainder 策略缺口补到文档宣称面 | 与 capability 叙述一致 |
| [svm-app-003](tasks/svm-app-003.md) | 非 Phoenix 小例子：Queue/Map/BitSet/Versioned 各一（证明 SDK 可复用） | Mollusk + 可选 Surfpool |

### Track E — 语义桥

| ID | 内容 | 验收 |
|---|---|---|
| [svm-sem-001](tasks/svm-sem-001.md) | Solanalib：operand materialization 或更大 CFG fragment correspondence | 有界定理；不声称 whole-program |
| [svm-sem-002](tasks/svm-sem-002.md) | assembler-semantics golden 与 ProofForge emit 差分扩样 | CI 可跑子集 |

### Track F — 工程

| ID | 内容 | 验收 |
|---|---|---|
| [svm-eng-001](tasks/svm-eng-001.md) | CI：`check_no_sorry` + 形式化相关 lake 目标进 SVM/Lean lane | PR 门绿 |
| [svm-eng-002](tasks/svm-eng-002.md) | 双矩阵收口：能力矩阵 + 形式化矩阵同一声明页 | 文档 + CI 摘要 |

---

## 6. 总看板

状态：`todo` / `doing` / `done` / `n/a`

| 轨道 | 片 | 状态 |
|---|---|---|
| A | sf-000 … sf-016 | 见形式化计划 §6（当前全 todo） |
| B | svm-rt-001 … 005 | todo |
| C | svm-sdk-001 … 007 | todo |
| D | svm-app-001 … 003 | todo |
| E | svm-sem-001 … 002 | todo |
| F | svm-eng-001 … 002 | todo |

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

## 8. 明确不做（写进计划，避免范围漂移）

- EVM Runtime/SDK 切片（另用 R4/R5）  
- WASM / XRPL / NEAR（PR 保持开）  
- sBPF ↔ 模型的全程序 refinement  
- 无界 `Array` / account 内 `HashMap` / 跨调用 heap  
- 未单开的 Token-2022 extension 静默兼容  
- 把 Phoenix 策略下沉进 SDK/Emit  

---

## 9. 开工建议（本周）

1. **主线**：`sf-000` → `sf-001`（Queue 非空 push）  
2. **并行一条能力缝**：`svm-rt-001`（signed Clock）或 `svm-sdk-001`（rent top-up）——选你更想先用的  
3. **顺手**：`svm-eng-001` 把 no-sorry 门钉进 CI  

能力片合并时：若引入新 SDK 表面，同步开/扩对应 `sf-*`，不要等「全部能跑了再证」。
