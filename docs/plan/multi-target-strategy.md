# 三 Target 推进战略（EVM · SVM · NEAR）

> 更新：2026-09-01。本文回答「接下来怎么继续往后做」：在 **XRPL 暂不管** 的前提下，
> 只推进 **SVM、EVM、NEAR** 三条线，并把 **Runtime/SDK 人体工程学** 作为横切目标。
>
> 继承：[runtime-sdk-roadmap.md](runtime-sdk-roadmap.md) ·
> [svm-work-plan.md](svm-work-plan.md) ·
> [analysis/near-runtime-sdk.md](analysis/near-runtime-sdk.md) ·
> [mainstream-parity.md](mainstream-parity.md) ·
> [parallel-workstreams.md](parallel-workstreams.md)

---

## 1. 总判断

ProofForge 当前不是「从零选 backend」，而是 **一条已通的 Lean→Extract→target IR→bytes 管道**
上，三条 target 处于不同成熟度：

| Target | 主分支状态 | 工程门 | 主要剩余 |
|---|---|---|---|
| **SVM** | R2/R3 大部分切片已集成；形式化刚起步 | Mollusk 435/435 · Surfpool | signed sysvar、Token-2022 extension、Phoenix 指令面、L3 语义桥 |
| **EVM** | R4/R5 大量 SDK/Runtime 已集成 | Anvil 41/41 · solc 0.8.34 | nested/wide dynamic ABI、signed math、ERC 扩展、**可选 verified backend** |
| **NEAR** | wasm-near 已 merge（PR #5） | near-sandbox 竖切 | 完整 NEP-141 公开面、Promise 泛化、collection metadata |

**推荐总序（不串行锁死，但依赖友好）：**

```text
横切 F0（shared substrate + 人体工程学）
    │
    ├─► SVM 主线（svm-work-plan Phase 1–7）
    ├─► EVM Feature A 收尾（R4/R5/R6 剩余 + solc 门）
    ├─► EVM Feature B 启动（powdr 三仓库 · 只作第二 backend / L3）
    └─► NEAR N12+（FT 公开 ABI → Promise 泛化 → 合流示例）
```

WASM 外分支（`wasm-feature` / XRPL）**保持开着、不阻塞、不合入本轨 PR base**（见
[svm-work-plan.md §3.2](svm-work-plan.md)）。

---

## 2. EVM：Feature A（主路径）与 Feature B（powdr 第二路径）

### 2.1 现状（Feature A = 当前主路径）

```text
普通 Lean def
    → Profile / Extract / Core CFG
    → Evm.IR
    → EmitYul
    → locked solc 0.8.34 --strict-assembly
    → .bin / .abi.json
    → Anvil 工程门
```

这与 [04-evm-feasibility.md](../research/04-evm-feasibility.md) 结论一致：**应该沿本仓薄 Yul
发射器 + solc 子进程做**，而不是 vendor 旧 PF DSL lowering。当前 Anvil 41/41、Token 等
examples 已证明工程链可用。

**Feature A 剩余（按 R4/R5/R6 + mainstream-parity F0–F2）：**

| 优先级 | 包 ID 建议 | 内容 | 验收 |
|---|---|---|---|
| P0 | [`evm-rt-nested-001`](tasks/evm-rt-nested-001.md) | nested/constructed/wide dynamic return 与 aggregate storage 组合 | Lean + solc + Anvil malformed matrix（wide/constructed **Anvil 已通**；aggregate storage 仍开） |
| P0 | `evm-codec-manifest-001` | per-method codec/memory resource manifest | Profile/Extract 稳定错误 |
| P1 | `evm-signed-001` | signed int 源类型 + 窄化 cast 词汇 | 双 consumer + Anvil |
| P1 | `evm-revert-bubble-001` | bounded revert bubbling / generic closed-call policy | 显式 fail-closed 边界文档 |
| F2 | `evm-erc-ext-001` | receiver callback、batch ERC-1155、indexed Address return | 独立 contract ×2 |
| R6 | `evm-conformance-001` | 与 SVM 对齐的 cross-target shared semantic fixtures | digest + CI lane |

**原则：** Feature A 继续占 **产品默认 `pf build --target evm`**；不为了 powdr 而改 Extract
合同。

### 2.2 powdr-labs 三仓库评估

| 仓库 | 是什么 | 与 ProofForge 的关系 |
|---|---|---|
| [evm-semantics](https://github.com/powdr-labs/evm-semantics) | Lean 4 **完整 EVM** 小步/大步关系语义；VMTests/EEST Conformance 全绿；含 gas、多帧、precompile | **L3 目标语义**（对标 SVM 的 solanalib） |
| [yul-semantics](https://github.com/powdr-labs/yul-semantics) | **Yul 大步语义**（无 gas）；可参数化 dialect；含 commit/rollback 观察边界 | **Yul 层正确性陈述**的中间语义 |
| [yul-compiler](https://github.com/powdr-labs/yul-compiler) | **已证明正确的 Yul→EVM bytecode** 编译器（含优化 pipeline）；Lake 依赖上述两库 | **solc 的可选替代 backend** |

三者的设计边界（来自各仓库 README）：

- yul-semantics **故意不建模 gas**；open-world `call/create` 在 `evmWithExternal` 下**无 executable interpreter**。
- yul-compiler 定理在 `fork = Osaka`、**顶层空栈**、且对 call/create 需 `ExternalsRealized` 假设下成立。
- yul-compiler **仍 reject `gas()`**；deep stack 靠 verified stack-layout / spilling fallback。
- evm-semantics 自标 **draft / not for production**；但 CI conformance 已是强工程证据。

### 2.3 建议：**引入，但作为 Feature B，不替换 Feature A**

**不要做的：**

- 不把 Extract 改成「先出 SemanticProgramV1 再喂 powdr」——与「定理钉用户 `def`」主合同冲突。
- 不把 powdr 三库 vendor 进 `ProofForge/Evm/*` Emit 主路径——体量大、fork 钉死、与 Component
  桥 ownership 冲突。
- 不宣称「Lean 定理 ⇒ 主网 bytecode 正确」——powdr 只缩小 **Yul→bin** 或 **bin 执行** 的
  TCB，不替代 Profile/Extract 正确性。

**应该做的（Feature B 阶梯）：**

| 阶段 | ID | 交付 | 验收 | 与 Feature A 关系 |
|---|---|---|---|---|
| **E-B0** | `evm-powdr-dep-001` | Lake git 依赖 pin `evm-semantics` + `yul-semantics` + `yul-compiler`（只读 lib target）；CI 只 `lake build` 依赖闭包 | 不拖慢主 Lean lane | 零运行时行为变化 |
| **E-B1** | `evm-yul-fragment-001` | 审计 ProofForge `EmitYul` 输出 ⊆ yul-compiler verified fragment；列 reject 清单（`gas()`、超深栈、未支持 builtin） | 脚本对比 + 文档表 | 指导 Emit 保持「可双编」子集 |
| **E-B2** | `evm-yulc-backend-001` | `pf build --target evm --backend=yulc`（或 env）；同一 `.yul` 走 yulc C API / CLI | Anvil 行为 diff：termination + storage + logs（**不比 bytecode 字节**） | 与 solc **并行**；默认仍 solc |
| **E-B3** | `evm-yulc-diff-001` | CI optional lane：Counter/Token/Capped 等 **双 backend** differential vs solc | 基线允许已知差异表 | 回归防 Fragment 漂移 |
| **E-B4** | `evm-l3-bridge-001` | 选定 emit 片段 ↔ `yul-semantics` `RunCommitted` / `evm-semantics` `Steps` 对应（Counter 级） | 有界证明或 assume+audit 边界明示 | 对标 SVM `svm-sem-*` |

**Feature A vs B 决策表：**

| 场景 | 用 solc (A) | 用 yulc (B) |
|---|---|---|
| 日常开发 / CI 默认 | ✓ | |
| 要缩小 assembler TCB | | ✓ |
| 合约含 `gas()` 或 yulc reject 片段 | ✓ | |
| 形式化/evidence 论文路径 | 可并存 | ✓（定理链更短） |
| StackTooDeep 已用 solc memoryguard 修过 | ✓（已验证） | 可试 yulc layout pass |

**结论一句话：** powdr 三仓库 **值得引入**，定位是 **「verified Yul 后端 + EVM L3 语义库」**，
不是 **「替代 Lean Extract」**。产品默认继续 solc；Feature B 与 SVM Track E（solanalib）对称。

---

## 3. SVM：按 svm-work-plan 收完 backlog

主分支 SVM 剩余已在 [svm-work-plan.md](svm-work-plan.md) §3–§4 钉死；此处只强调 **与三
target 并行的切片优先级**。

### 3.1 六轨并行（摘要）

| 轨 | 下一刀 | 任务 ID |
|---|---|---|
| **A 形式化** | SF-1..4a **done**；SF-4b partial → Allocator/Map | `sf-007`… |
| **B Runtime** | signed Clock · Instructions sysvar · alias-aware variable walk | `svm-rt-001`…`003` |
| **C SDK** | rent top-up · Token-2022 extension facade · runtime-selected Memo | `svm-sdk-001`…`003` |
| **D 应用** | Phoenix CancelUpTo 8/9 · fee 用 `Core.Math` | `svm-app-001`…`002` |
| **E L3** | operand materialization · `.s` golden | `svm-sem-001`…`002` |
| **F 工程** | 形式化进 CI · manifest | `svm-eng-001` |

### 3.2 与 NEAR/EVM 的隔离规则

- SVM PR **禁止**以 `wasm-near` / `wasm-feature` 为 base。
- WASM 合 main 时只做 [svm-work-plan §3.2](svm-work-plan.md) 窄缝（`Svm/IR.lean` reject 臂、
  README 表合并）。
- 共享层改动（Extract/Core）走 **coordinator + shared-lock**（见
  [parallel-workstreams.md](parallel-workstreams.md)）。

### 3.3 外部分支 `cursor/svm-phase1-queue-eab6`

该分支含 Phoenix tag-10、Token-2022 E∞ 等实验；**不合入本战略默认序**。若 cherry-pick，必须
独立 PR + 全 Mollusk/Surfpool 回归，且不改变 NEAR/EVM registry 合同。

---

## 4. NEAR（WASM）：N12 起的公开面与 Promise 泛化

NEAR 已在 main（PR #5）。能力计划权威来源：[analysis/near-runtime-sdk.md](analysis/near-runtime-sdk.md)。

### 4.1 已完成（N0–N11 摘要）

- Host context、u128、arena、bounded Borsh/JSON 输入输出
- Storage KV、Vector/Lookup/Iterable/Queue 基础布局
- Promise 静态链、transfer、self-callback、两路 join
- FT ledger + storage economics 竖切（deposit/withdraw/unregister/force）
- 大量 **parser-only** JSON 帧（ft_transfer、transfer_call、on_transfer、resolve）

### 4.2 剩余工作（按依赖排序）

**N12 公开 FT 面（2026-09-01 状态：已在 `Examples.NearFungibleLedger` 落地）**

- `ft_transfer` / `ft_transfer_call` / `ft_resolve_transfer` + storage 全套 + NEP-141 events
- near-sandbox 矩阵见 `runtime-tests/near/ledger.py`
- **剩余**：Promise 泛化（N13）、collection metadata（N14）、三 target conformance（N15）

| 阶段 | ID | 交付 | 前置 | 验收 |
|---|---|---|---|---|
| ~~**N12**~~ | ~~`wsm-near-ft-*-export`~~ | ~~公开 FT 面~~ | ✓ merge | sandbox ledger |
| **N13** | [`wsm-near-promise-general-001`](tasks/wsm-near-promise-general-001.md) | 有界 Promise handle、N 路 join（仍 fail-closed 上限） | N12 | DAG sandbox ✓（handle SDK step 1；**3..8-way `andN` + promise.py** ✓；compile-time `maxFanIn` beyond N=8 仍开） |
| **N14** | `wsm-near-store-meta-001` | collection prefix/metadata（仍 **不** 冒充 near-sdk `Drop`/cache） | N5 基础 ✓ | layout golden |
| **N15** | `wsm-near-conformance-001` | Counter/Token 形 cross-target 示例（SVM/EVM 已有对照） | N12d | 三 target digest 表 |

**明确不做（与计划一致）：**

- 通用 serde_json / 任意 JSON object graph
- 同步跨合约调用假象
- TreeMap（除非 NEP 标准强制且有人消费）
- 主网部署声明

### 4.3 NEAR 人体工程学（见 §5）优先于 N14 的「更多容器名」。

---

## 5. 合约人体工程学：Runtime SDK 向「传统语言」靠拢

目标不是复制 Solidity/Rust 语法，而是 **在普通 Lean 里减少机械噪声**，同时保持 fail-closed
与「定理钉 `def`」。

### 5.1 现状痛点

| 区域 | 今天 | 像传统语言还差什么 |
|---|---|---|
| 状态 | 每个 entry 显式 `(s : State)` | 无 `mut s` / implicit state threading |
| 错误 | `Except Error (State × τ)` 手写 | 无 `?` / `do` 块统一传播 |
| 宽整数 | NEAR `NearToken.w0/w1`；EVM 部分仍 limb 思维 | 统一 `UInt128`/`NearToken` 运算符面 |
| 存储 | EVM `Storage.Layout` 较好；SVM account field；NEAR 仍偏 runtime 名 | 三 target 统一 **handle + 方法** 命名 |
| 导入 | `ProofForge` / `ProofForge.Evm.Sdk` / `ProofForge.Wasm.Near.Sdk` 分裂 | 单入口 + target 擦除 |
| 效应 | `Runtime.nearTokenAddW0` 等泄漏 | SDK 层完全隐藏 runtime stub 名 |

### 5.2 横切 Ergonomics 包（建议 ID `erg-*`）

| ID | 交付 | 范围 | 原则 |
|---|---|---|---|
| **erg-do-001** | 共享 `Except` 的 `ok`/`err`/`andThen`/`map`/`guard` | Core + Examples | EVM/SVM/NEAR `andThen` 示例已通；NEAR mutating JSON u128 `NearToken` 返回已通 |
| **erg-near-token-001** | `NearToken` 高层 API：`isZero`/`le`/`lt`/`add?`/`sub?`/`mulUInt64?`/`addChecked` 等 | Near.Sdk + `NearTokenErgonomics` | limb 级 op 复用既有 Runtime |
| **erg-evm-effect-001** | `Evm.CallResult` / `Effect.then` 链式文档 + Token 示例改写 | Evm.Sdk | 已有 R5-012 能力，只改 surface |
| **erg-svm-account-001** | `Account.Handle` 方法链（`.transferLamports`、`.resizeData`、`.closeTo`）示例化 | Svm.Sdk | 已有 R2/R3，补 cookbook |

### 5.3 「像传统语言」的验收标准（可测）

1. **Counter 级 example**：entry 函数体 **不出现** runtime stub 名、limb 名、重复 `s` 传递。
2. **Token 级 example**：mint/transfer 读起来像 **顺序语句 + early return**，不是嵌套 `match`。
3. **三 target 各 1 个「cookbook」文件**，CI 只检查能 `pf build` + 原 runtime 测试仍绿。
4. **Import guard**：`Examples/*` 禁止 `ProofForge.*.Runtime` / `*.Emit`（扩展现有 ownership）。

### 5.4 排期建议

- **与 F0 shared substrate 并行**：`erg-wide-001`、`erg-sdk-facade-001` 不挡 R2/R4。
- **NEAR N12 前完成 `erg-near-token-001`**：否则 FT 公开 API 会固化 limb 风格。
- **`erg-state-001` 最后做**：需要 Profile/Extract 变更，走 coordinator lock。

---

## 6. 推荐执行顺序（接下来 8 个可独立 PR 的切片）

下列每一项 = 一个 branch + 一个 PR + 完整验收；可并行但遵守
[parallel-workstreams.md](parallel-workstreams.md) write set。

| 序 | 分支主题 | 主要文件 | 门 |
|---|---|---|---|
| 1 | SVM Queue 形式化收口 | `ProofForge/Svm/StorageModel/*` | Lean + sf 矩阵 |
| 2 | SVM signed Clock | `ProofForge/Svm/Sysvar/*` | Mollusk |
| 3 | EVM nested dynamic return | `ProofForge/Evm/Codec/*` | Anvil |
| 4 | NEAR `ft_transfer` 公开 export | `ProofForge/Wasm/Near/*` + sandbox | near-sandbox |
| 5 | Erg NearToken surface | `ProofForge/Wasm/Near/Sdk.lean` | Lean + build near |
| 6 | EVM powdr dep pin (E-B0) | `lakefile.lean` + `docs/plan/tasks/evm-powdr-dep-001.md` | CI build deps |
| 7 | EVM yul fragment audit (E-B1) | `scripts/check_yul_fragment.py` | script self-test |
| 8 | SVM L3 sem-001 straightline | `ProofForge/Svm/Solanalib.lean` | Lean |

**Coordinator 职责不变：** 任何 touch Extract/registry/docs/plan 的 PR 由集成者合并；worker 返回
SHA + 证据。

---

## 7. 文档与 backlog 同步

完成每个切片后更新：

- [backlog.md](backlog.md) — 工程证据一行
- [runtime-sdk-roadmap.md](runtime-sdk-roadmap.md) — 仅当阶段边界变化
- [docs/plan/tasks/](tasks/) — 新 task md
- [capability-matrix.md](capability-matrix.md) — 新 capability 行

本文 **不替代** `runtime-sdk-roadmap.md` 的 R0–R6 权威排期；只补充 **三 target 并行视角** 与
**EVM Feature B（powdr）** 决策。

---

## 8. 风险与诚实边界

| 风险 | 缓解 |
|---|---|
| powdr toolchain / Mathlib 版本与 ProofForge pin 冲突 | E-B0 先只 pin dep，不 link 主 `pf` |
| yulc 与 solc 行为 diff | 双 backend CI + 基线表；默认 solc |
| 三 target 抢 Extract shared-lock | parallel-workstreams coordinator 队列 |
| Ergonomics 糖破坏 extract 确定性 | 每个 `erg-*` 必须钉 IR digest 测试 |
| NEAR「几乎 NEP-141」被误读为兼容 | 每个 export task 写 compatibility diff 段 |

**Trust boundary 不变：** 内核定理仍只钉用户 `def` / IR；Anvil/Mollusk/near-sandbox 是工程门；
powdr 至多把 **Yul→bin 或 EVM 执行** 纳入可证链条，不自动 uplift 到部署正确性。
