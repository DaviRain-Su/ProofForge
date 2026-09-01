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
| D 应用 | `Examples.Phoenix*` 指令与 matching | Runtime leaf / recipe opcode | 只组合已有 SDK |
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
| E1 | operand materialization + 多指令 straightline | 真实 Counter emit 片段可模拟 | `svm-sem-001` |
| E2 | `.s` golden ↔ `sbpfSemantics` 解析/步进 | 全 corpus / 选定程序差分门 | `svm-sem-002` |
| E3 | 整函数 CFG（有界 block）end-to-end correspondence | Counter increment 全路径 | `svm-sem-003` |
| E4 | 账户字模型（Track A）与 sBPF 内存 store 的桥 | `AccountWords` write ≡ typed `storev`（有界） | `svm-sem-004` |
| E5 | 多入口程序 / 简单容器例（Queue push 空路径） | 选定 Examples 全函数有界证明 | `svm-sem-005` |
| E∞ | Loader-v3 + syscall/CPI/sysvar 主机 + ELF 接受 | Agave 忠实全程序 | **不承诺为本轨完成条件** |

**E0–E5 要规划、要做完。** E∞ 留作远景：缺主机模型就无法诚实声称；不挡 E0–E5 收口。

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
| 语义桥 / L3 | checked arith / CFG branch correspondence；assembler-semantics golden（E0） | E1–E5：operand materialization、整函数 CFG、AccountWords↔storev、容器例 |
| 工程 | 三 lane CI、406 Lean jobs、67 SVM / Mollusk 全绿 | 形式化门进 CI、artifact/digest 漂移说明、计划矩阵自动化可选 |

---

## 4. 推荐总序（给人排期用）

不必严格串行；下列是 **依赖友好** 的默认顺序。括号内是并行建议。

```text
Phase 0   导航对齐
          · 读本文 + formalization-plan + mainstream-parity §4–5
          · 确认 WASM PR 不阻塞

Phase 1   证明主线启动 + L3 阶梯启动 + Runtime 小缺口   ← 立刻
          · A: sf-000 → sf-001 → sf-002（Queue 收口）
          · E: svm-sem-001 operand materialization / straightline（可并行）
          · B: svm-rt-001 signed Clock（可并行）
          · F: svm-eng-001 形式化 CI 门（可并行）

Phase 2   持久容器证明 + SDK lifecycle + L3 golden 门
          · A: sf-003..sf-005（Vec / Versioned / BitSet）
          · E: svm-sem-002 assembler-semantics corpus 差分门
          · C: svm-sdk-001 rent top-up + close 政策收口
          · C: svm-sdk-002 owner-reassign 显式政策（fail-closed 边界写清）

Phase 3   Transient 证明 + SDK 形状加宽 + Counter 全函数 L3
          · A: sf-006..sf-007（TransientModel）
          · E: svm-sem-003 Counter increment 有界 CFG end-to-end
          · C: svm-sdk-003 generic POD transient record shapes
          · C: svm-sdk-004 更多 manifest-bounded transient slots

Phase 4   Map/Tree 证明 + Token-2022 + 内存桥
          · A: sf-008..sf-011（Allocator/Map/EnumerableSet/Tree）
          · E: svm-sem-004 AccountWords ↔ typed storev 桥
          · B/C: svm-rt-002 + svm-sdk-005 Token-2022 第一批 extension
                （transfer-fee 或 mint-close-authority，选一个有双 consumer 的）

Phase 5   Component 组合证明 + Phoenix 指令面 + 容器 L3
          · A: sf-012..sf-013（FifoCancel / BatchRecorder）
          · E: svm-sem-005 Queue empty-push（或选定容器）全函数有界证明
          · D: svm-app-001 Phoenix-v1 下一指令族（在现有 SDK 上组合）
          · D: svm-app-002 matching/fee 缺口补片（仍只在 Examples）

Phase 6   Facade 扫尾 + 序列化/返回政策
          · A: sf-014..sf-015
          · B: svm-rt-003 nested/wide dynamic return（若仍在 ceiling 内）
          · C: svm-sdk-006 UTF-8 Memo / richer migration payload

Phase 7   收口
          · A: sf-016 形式化审计
          · E: E0–E5 看板全绿（E∞ 可仍为远景 n/a）
          · F: svm-eng-002 SVM 能力+证明+L3 三矩阵声明
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

### Track E — L3 sBPF 语义桥（阶梯 E0–E5）

依赖：已 pin 的 `solanalib` + `sbpfSemantics`（assembler-semantics）。E0 已有基线。

| ID | 阶 | 内容 | 验收 |
|---|---|---|---|
| （基线） | E0 | checked arith / store / branch fragment ↔ Solanalib `step` | **已有** |
| [svm-sem-001](tasks/svm-sem-001.md) | E1 | operand materialization + 多指令 straightline | 真实 Counter emit 片段可在 Solanalib 下模拟 |
| [svm-sem-002](tasks/svm-sem-002.md) | E2 | `.s` golden ↔ `sbpfSemantics` 解析/步进差分门 | CI 可跑 corpus 子集；失败可定位 program |
| [svm-sem-003](tasks/svm-sem-003.md) | E3 | 整函数有界 CFG end-to-end（Counter increment） | success/overflow 全路径 correspondence |
| [svm-sem-004](tasks/svm-sem-004.md) | E4 | Track A `AccountWords` ↔ typed `storev` 内存桥 | 有界槽写读一致；不声称任意地址 |
| [svm-sem-005](tasks/svm-sem-005.md) | E5 | 选定容器例全函数（建议 Queue empty-push） | 与 sf-001/002 同一主语；有界证明 |
| — | E∞ | Loader-v3 + syscall/CPI/sysvar 主机 + ELF 接受 | **远景**；非本轨完成条件 |

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
| E | svm-sem-001 … 005（E0 已有） | todo |
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

1. **主线证明**：`sf-000` → `sf-001`（Queue 非空 push）  
2. **主线 L3**：`svm-sem-001`（接住已有 Solanalib 基线往 E1 走）  
3. **并行能力缝（可选）**：`svm-rt-001` 或 `svm-sdk-001`  
4. **顺手**：`svm-eng-001` 把 no-sorry 门钉进 CI  

能力片合并时：若引入新 SDK 表面，同步开/扩对应 `sf-*`，不要等「全部能跑了再证」。
