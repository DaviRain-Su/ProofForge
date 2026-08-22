# Lean 4 直写 Solana 合约：可行性结论

> Date: 2026-08-22
> Core question: 能否把 Solana 从 ProofForge 剥离，用普通 Lean 4 语法（不新设计合约语言/DSL）写合约，完整复用 Lean 4 形式化验证，并经汇编/FFI 落到可部署的 Solana 程序？
> Related docs: [00-research-plan.md](00-research-plan.md) · [01-working.md](01-working.md) · [02-dimension-6-audit.md](02-dimension-6-audit.md)
> Exploration: 4 轮；关键部署/剥离/对照已实测或交叉引用；路径 B 抽取器尚无原型

---

## 一、结论（先看这个）

**能做独立 `solana-lean`，但不能按用户原方案的那条编译链做。**

| 用户原话 | 判定 | 根因 |
|---|---|---|
| 从 ProofForge 单独剥离 Solana | **有条件可行** | Solana 目标已能编出并可被 Mollusk 执行；剥离是 curated fork，import 闭包约 **212 文件 / 16.7 万行**，不是抠一个发射器 |
| 用 Lean 4 语法写合约，不新设计合约语言/DSL | **有条件可行** | 可行的是「普通 `def` + attribute + fail-closed 子集」；不可行的是「任意 Lean 都能编」。ProofForge 今天用的是自定义 `program ... where`，那是新具体语法 |
| 完全复用 Lean 4 形式化验证 | **对所选语义可行；对已部署 `.so` 当前不可** | Lean kernel 可以检查关于 Reference / 普通 Lean 函数的定理；没有一般 refinement 连到 ELF/loader/SVM。Formal D1–D4 仍是 0/27 |
| 利用 Lean FFI，先编到汇编，再调工具生成合约 | **不可行** | FFI 是 C ABI 互操作，不是编译后端；Lean 生成的是带 `lean.h`/RC 堆的宿主 C；宿主汇编不是 sBPF |

正确编译路径是：

```diagram
┌──────────────────────┐
│ Lean 源（A: program  │
│ where 或 B: 受限 def）│
└──────────┬───────────┘
           ▼
┌──────────────────────┐
│ 抽出/校验后的语义 IR  │  ← 定理主语必须钉在这里
└──────────┬───────────┘
           ▼
┌──────────────────────┐
│ Solana Plan/HandlerIR │
│ → emitSbpfAsmV1 (.s)  │
└──────────┬───────────┘
           ▼
┌──────────────────────┐     ┌─────────────┐
│ Lean IO 子进程        │────▶│ locked sbpf │
│ （不是 FFI）          │     │ → .so       │
└──────────────────────┘     └──────┬──────┘
                                    ▼
                             Mollusk / 本地 SVM
```

---

## 二、现状（数字，不是形容词）

### ProofForge 今天怎么写合约

用户写的是 Lean **自定义命令**，不是普通函数：

```lean
program TransferSol where
  requires extension solana.cpi.accounts version "1.0.0"
    digest "sha256:…"
  entry transfer(payer : Principal, recipient : Principal, lamports : UInt64) : UInt64 do
    call solana.system.transfer(payer, recipient, lamports)
    return lamports
```

- 语法：`declare_syntax_cat pfType/pfExpr/pfStmt` + `syntax (name := programDecl) "program " ident " where" …`
  - [`ProofForgeV2/Language/Syntax.lean`](file:///Users/davirian/orca/projects/proof_forge/ProofForgeV2/Language/Syntax.lean)
- 精化：`elab_rules` 解码成 `ValidatedSourceV1`，再 Normalize 成 `SemanticProgramV1`
  - [`ProgramElaborationV1.lean`](file:///Users/davirian/orca/projects/proof_forge/ProofForgeV2/Language/ProgramElaborationV1.lean)
- ADR-0002 否决的是无约束 `StateM`/任意 host 计算，不是「凡是普通 Lean 表面都不行」
  - [`docs/adr/0002-unified-program-dsl.md`](file:///Users/davirian/orca/projects/proof_forge/docs/adr/0002-unified-program-dsl.md)

同一文件里的 `theorem` 才是普通 Lean。定理主语是抽出的 `SemanticProgramV1`，不是源级 `def`。

### 「不用新 DSL」必须拆成三档

| 档 | 表面 | 抽出 | 判定 |
|---|---|---|---|
| (a) 新具体语法 | `program … where` | 可以（PF 已做） | 这就是新 DSL |
| (b) 普通 Lean + `@[solana_entry]` + 传递闭包校验 | 看起来像 Lean | 可以，前提 fail-closed | **这是「不新设计语言」的唯一诚实读法** |
| (c) 无约束 Lean | 任意 `def`/`IO`/`partial` | 不能声称语义完整 | 不可行 |

路径 (b) 在形式意义上仍是语言子集（可接受程序的集合有自己的规则）。用户不学新关键字；编译器必须拒绝递归、`sorry`、`@[extern]`、`@[implemented_by]`、无界分配、传递依赖里的 axiom。

Lean 可以在 elaboration 之后用 `getConstInfo` 读到 `DefinitionVal.value`（elaborated `Expr`）。抽出权威应是这个闭包，不是 LCNF/`Lean.Compiler.IR`（后者已擦除 dependent type，且是版本钉死的内部 API）。

### Lean 编译器实际产出什么

本机 Lean **4.33.1**（`lean --help`）：

- `-o` `.olean`，`-i` `.ilean`，`-c` C，`-b` LLVM bitcode
- **没有** Coq 那种 Extraction 命令
- 当前 C 后端走 `Lean.Compiler.LCNF.emitC`（`Shell.lean:559-572`）
- FFI 官方定义：`@[extern]` 让编译后的 Lean 调 C 符号；`@[export]` 让 C 调 Lean。不是 ISA 选择，也不是 codegen hook
  - https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/
- 生成 C 立刻 `#include <lean/lean.h>`，调用 `lean_alloc_ctor` / `lean_inc` / `lean_dec`。实证：`proof_forge/.lake/packages/assembler-semantics/.lake/build/ir/SbpfSemantics/Api.c`
- LLVM emitter 源码写明：「our CI for LLVM is dysfunctional so this code is not actually tested」
  - https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/Compiler/IR/EmitLLVM.lean

Solana 官方限额（不要和 Lean 堆搞混）：

| 资源 | 官方值 |
|---|---|
| 默认堆 | 32 KiB |
| 可调最大堆 | 256 KiB |
| **每帧**栈 | 4,096 bytes |
| 最大调用深度 | 64 |

https://solana.com/docs/core/programs

把 Lean 生成 C 丢给 Solana Clang：预期先死在缺 `lean.h` 和 sBPF 版 Lean runtime。未做端到端编译实验。

### Solana 物化路径（已跑通工程车道）

```
ValidatedSourceV1
  → CompiledSemanticV1 / SemanticProgramV1
  → Solana Plan
  → HandlerIR
  → emitSbpfAsmV1 → {name}.s
  → Lean IO: sbpf.build -d <deployDir>
  → {name}.so
```

- 发射器产出真实 sBPF 文本（`.equ` / `entrypoint` / `ldxdw` / `call` / `exit`），不是伪汇编
- `sbpf` = Blueshift **0.2.2**，commit `d835bc6e638e4f55b88f31a31bbc92e3a2e0a5ba`，**子进程**，不是 FFI
- assembler-semantics pin：`ef6e20c20827e4158e1cb025518465aa8beb46da`
- 无 Anza platform-tools 产品路径

**Mollusk 实测（2026-08-22，本调查）**

```
PROOF_FORGE_SOLANA_TEST_OUT=…/StateCell
cargo test --locked --test state_cell_shaped_product -- --nocapture
→ 5 passed; 0 failed
```

`StateCell.so`：`ELF 64-bit LSB shared object, eBPF`，SHA 与 manifest 一致。Mollusk Loader V3 直接吃 ELF 字节。断言覆盖：

- `initialize` 写回 count=5
- `increment` 成功、return 8、账户 count=8
- `get` 成功、账户不变
- overflow：`Custom(0x1001)`，状态保持 `u64::MAX`

**没有**公开 Devnet/Testnet/Mainnet 部署证据。`pf deploy` 明确只打本地回环。Surfpool 有本地链 smoke，本轮未复现。

### 形式化验证今天钉在哪一层

至少五层，不要混：

1. 业务语义：`SemanticProgramV1` + `ReferenceMachineV1`
2. 目标 IR：Solana Plan / `HandlerIR`
3. 解析后 ISA：生产 `.s` → `SbpfSemantics`
4. 制品：ELF / linker / loader
5. 运行时：SVM / Agave / Mollusk 观察

用户 `invariant` / `preserving` 定理谈的是第 1 层。

- `InvariantTheoremV1`：所有 conforming 逻辑状态上不变量为 true。**不含**可达性
- `PreservationTheoremV1`：admission 成功 + 初态/init + 一步保持；revert/trap 不改状态
- Formal TASK D1–D4：**0/27**。inline proof 是工程门禁
- 有界证书已有：若干 UInt64 recipe 的 Reference→HandlerIR；StateCell 四场景 HandlerIR↔identity-bound `.s`（55/55/70/56 steps）。**一般 lowering / ELF / SVM 未证**
- `Examples/MiniAmmL1.lean` HEAD 只有 invariant，没有 theorem。ADR-0034「product certifier GREEN」过时

### 剥离规模

仓库快照 `ac7f0db485c6436cd51c17c7db6e4f558a416b5e`。从 `Targets/Solana/*.lean` BFS `^import `：

| 范围 | 文件 | 行 |
|---|---:|---:|
| 仅 Solana | 56 | 57,100 |
| **import 精确闭包** | **212** | **167,472** |
| 目录并集（Solana+Semantic+Typed+Compiler+Language+Source+Core+Materialization） | 219 | 167,476 |
| 整个 ProofForgeV2 | 342 | 272,193 |

闭包内：Semantic 63 / Typed 12 / Compiler 5 / Language 6 / Source 43 / Core 11 / Materialization 4 / 其它 Targets 10 / Examples 夹具 2。内部 import 0 未解析。

未计入：Lean/Std、`assembler-semantics` 传递源、C extern、工具链。数字是下界。

`clients/solana-client` 已是独立 Rust crate，只做 OutputSet/ABI 离线校验，不是编译器。

---

## 三、对照：别人怎么切「写什么 / 证什么 / 部署什么」

完整 13 条失败模式与出处见 [02-dimension-6-audit.md](02-dimension-6-audit.md)。

| 系统 | 写法 | 验证主语 | 部署物 | 和本方案的关系 |
|---|---|---|---|---|
| Certora CVL | Solidity + CVL 规格 | 合约/字节码 | 原编译器产物 | CVL **不**编到链上；Solana 版甚至直接分析 SBF |
| Kani / Prusti / Creusot | Rust | Rust/MIR 编码 | rustc 产物 | 验证生产语言，不发明部署语言 |
| Move Prover | Move + 规格 | Move 字节码 | Move VM | 语言/VM/验证器共设计 |
| Cairo + Lean | Cairo；Lean 做语义 | Cairo VM/AIR | Cairo 制品 | Lean **不**部署 |
| ConCert | 受限 Coq 模型 | Coq 执行模型 | 抽到 Liquidity/LIGO/Rust | 最接近「抽取」；最终编译器常在 TCB |
| Seahorse | 类 Python | 无正式 FV | 生成 Rust→Anchor→SBF | 自称 beta，非生产 |
| Solang | Solidity | 无内建 FV | LLVM→SBF | 项目已 archive |
| ProofForge | 受限 DSL + 普通定理 | `SemanticProgramV1` | `.s`→`sbpf`→`.so` | 诚实分层；不声称 `.so` 精化 |

2026-08-22 检索记录（见 D6 文档）：**在这些检索里没有找到生产级 Lean→sBPF 编译器**。这不是全域不存在声明。

反复失败的等式：

> kernel 接受了一条源定理 + 随便一个后端 = 已部署链上程序被证明

漏掉的是：表示/定宽算术/效应/ABI/编译保持/汇编器/ELF/loader/host/计量/制品同一性。

---

## 四、缺口（按优先级）

| 优先级 | 现状 | 别人怎么做 | 建议 |
|---|---|---|---|
| P0 编译链概念 | 用户方案把 FFI 当后端 | 所有可比系统都把「证明语言编译」和「C ABI」分开 | **否决 FFI→asm**。发射自研 IR，汇编用 locked `sbpf` 子进程 |
| P0 验证主语 | 定理钉 Reference，部署是 `.so` | Certora 直接分析 SBF；Cairo 证编译关系 | v0 诚实声明：证的是语义 IR。`.so` refinement 另立项，不写进首发承诺 |
| P1 「普通 Lean」前端 | 只有架构，无抽取器原型 | ConCert / Aeneas 都先钉子集再抽 | 若要「没有自定义关键字」，做路径 B，且必须 fail-closed；先不要承诺无约束 Lean |
| P1 剥离成本 | 闭包 16.7 万行 + 外部 assembler-semantics | — | 独立仓 = 版本冻结的 curated fork，不是从 PF 活跟踪 |
| P2 部署面 | Mollusk 强；公开网零 | PF 自己禁止公网广播 | v0 以 Mollusk + 可选本地 Surfpool 为验收，不谈主网 |
| P2 CPI/PDA | PF 有工程夹具，非产品精化 | Anchor 也只是框架约束 | v0 单账户；CPI 只允许具名封闭 recipe |

---

## 五、验证记录

| 断言 | 方法 | 结果 |
|---|---|---|
| PF 用自定义 `program` 语法 | 读 Syntax.lean / Elaboration / Examples | 确认 |
| ADR-0002 否决无约束 StateM | 读 ADR:47-50 | 确认 |
| Lean 无 Extraction；有 -c/-b | `lean --version` / `lean --help` | 4.33.1；无 extract 旗标 |
| FFI 不是后端 | 官方 FFI 手册 | 确认 |
| 生成 C 依赖 lean.h / RC | 读 `SbpfSemantics/Api.c` | `#include <lean/lean.h>`；`lean_inc`/`lean_alloc_ctor` |
| EmitLLVM CI 坏 | 读 lean4 v4.33.1 EmitLLVM.lean | 原文确认 |
| Solana 堆/栈限额 | solana.com/docs/core/programs | 32KiB 堆；每帧 4KiB 栈 |
| 产品路径 Plan→.s→sbpf→.so | 读 ProductionPreparationV1 / FinalizeV1 / EmitSbpfAsmV1 | 确认；`sbpf.run #["build","-d",…]` |
| StateCell.so 可被 SVM 执行 | `cargo test --test state_cell_shaped_product` | **5/5 pass**；写回/overflow 均断言 |
| 公网部署 | 读 pf-cli deploy.rs / walkthrough | 明确禁止；无证据 |
| Formal 0/27 | MIGRATION_MATRIX.md:9-37 | 确认 |
| MiniAmmL1 无 theorem | 读源 + 全仓搜 | HEAD 只有 invariant + Admit 测试 |
| 剥离闭包 | Python BFS import | 212 files / 167,472 LOC |
| 无生产 Lean→sBPF | 2026-08-22 记录检索 | 未找到；非全域否定 |
| 路径 B 抽取器可工作 | — | **[UNVERIFIED] 无原型**（不影响「有条件可行」判定，只影响工期） |
| 生成 C + Solana Clang 的首个链接失败 | 未实验 | **[UNVERIFIED]**；已有 header/runtime 证据足够否决「直接编」 |

---

## 六、若做独立 `solana-lean`：最小架构

### 两条前端，一条后端

**路径 A（先出活）**：复用 PF 的 `program … where`

```
program where → decoder → ValidatedSourceV1 → Check/Normalize
  → SemanticProgramV1  （定理钉这里）
  → Plan → HandlerIR → emitSbpfAsmV1 → .s → sbpf → .so
```

**路径 B（长期 UX）**：普通 Lean 子集

```
@[solana_entry] def increment … → elaborator → Expr 闭包
  → 新 fail-closed 子集检查 → 新抽出器 → 同一语义 IR
  → 同一发射器 / sbpf
```

`Solana.Contract` 必须是惰性数据，不能是可执行 host builder，否则退回 ADR-0002 否决案。

### v0 做 / 不做

**做**

- 一个 Solana target，一个 locked `sbpf` profile
- `UInt8/32/64`、条件、checked 算术、单账户、init/entry/view
- Lean 定理钉在语义 IR / 普通 Lean 转移函数
- 确定性 `.s`、制品 digest、负向子集测试、Mollusk smoke

**不做**

- EVM/NEAR/其它链
- Lean FFI→汇编
- 无约束 Lean、`IO`、一般递归、动态分配
- 「定理蕴含已部署 `.so`」
- 通用 CPI/PDA、多可变账户、Token/ATA
- 公网部署

### 搬什么 / 重写什么

| 搬（vendor 冻结快照） | 重写 |
|---|---|
| Solana Plan/IR/EmitSbpf/Finalize | 独立 CLI / 包布局 |
| 语义 IR、checked 算术、账户布局 | 路径 B 的 attribute + 闭包检查 + 抽出器 |
| locked-tool 解析 | Solana-only 配置与 manifest |
| 有界 SBPF 证书（可选） | 诊断面向普通 `def` |
| Mollusk harness / 黄金 `.s` | 删掉多 target registry / 治理机械 |

路径 A 还要带上 Language/Source/Typed/Normalize。路径 B **不要**搬 Syntax/Elaboration/Normalize。

### TCB（部署行为声明）

两边在 frontend 以下几乎相同：

`kernel → elaborator → (A: decoder/Normalize | B: checker/extractor) → materializer → emitter → sbpf → loader → SVM`

弱声明「kernel 接受了关于所选语义的定理」只需要 kernel + 主语绑定正确。不要把 Mollusk 绿当成这一层。

### 决策规则

- 优先「写起来像 Lean，不要自定义关键字」→ **B**（12 个月级，先做差分验证）
- 优先「尽快出可编译、可证的 Solana 程序」→ **A**（3 个月级）
- 两边都立刻要 → 先 A，B 作为第二前端，**同一 semantic IR 必须字节级对齐** 共享夹具

3/6 个月 A 明显便宜。12 个月只有当「普通 Lean UX」是长期差异化时，B 才可能更便宜。

### 会杀死项目的事（不是延期）

1. B 的传递闭包不能 fail-closed
2. 证明主语和编译主语不是同一个 semantic hash
3. 发射器静默降级 / 丢指令
4. 账户 ABI / 别名 / 写回未定义
5. `sbpf` ELF 不被目标 loader 接受（当前 Mollusk 已接受 StateCell；换汇编器或换 SVM 版本要重新资格）
6. 干系人把 `.so` refinement 当 v0 必达
7. 通用 CPI/PDA 当 v0 必达
8. 无法冻结上游 PF，活跟踪 16 万行
9. 没有对抗性 SVM 回归

---

## 七、建议的下一步（可执行）

1. **先定产品句**：独立仓 v0 =「Lean 里写受限合约 + kernel 检查语义定理 + 工程编译到 Mollusk 可跑的 `.so`」。明确不包含 FFI 后端、不包含 `.so` 精化。
2. **先做路径 A 的 curated fork**：按 import 闭包冻结 PF 快照 + `assembler-semantics` + `sbpf 0.2.2`；砍掉非 Solana target。验收：StateCell 5 测仍绿。
3. **钉死语义 IR 边界**（hash / 规范 / 负向集）。这是以后换前端的唯一接缝。
4. **若要坚持「没有 `program` 关键字」**：另开路径 B，用 Counter 单账户做纵向原型（检查→抽出→与 A 的 IR 字节对比→同一 `.s`）。没有这个原型之前，不要对外说「已经是普通 Lean」。
5. **不要**尝试 Lean C/LLVM → Solana Clang，也不要在 v0 接通用 CPI。

---

## 八、盲区

- 路径 B 抽取器没有原型；「普通 Lean 可抽出」是架构可行性，不是工期保证
- 传递闭包未计入 Lean/Std、assembler-semantics 源码、C extern
- 未把生成 C 真正丢给 Anza Clang（对否决「直接编」不是必需，对「移植 runtime」才需要）
- TransferSol 的 Mollusk 套件本轮未跑（源码路径与 StateCell 相同，未复现）
- 未复现 Surfpool 本地部署；无跨主机 `sbpf` 可复现性实验
- 未审计 Blueshift `sbpf` 与 Anza SVM 的指令级一致性
- 未评估许可证是否允许把 PF 闭包搬进独立仓对外发布
