# Research Plan: Lean 4 直写 Solana 合约可行性

> Core question: 能否把 Solana 从 ProofForge 剥离，用普通 Lean 4 语法（不新设计合约语言/DSL）编写合约，完整复用 Lean 4 形式化验证，并经汇编/FFI 落到可部署的 Solana 程序？
> min_rounds: 3

## Dimensions

1. **语言面（“不用新 DSL”的真实含义）** — ProofForge 现有 `program ... where` 是 Lean custom syntax，不是普通 Lean 函数；要判断“纯 Lean 4 语法”与“Lean 上的受限 DSL”差在哪，以及前者能否静态抽出可编译语义。
2. **形式化验证复用** — Lean 4 核验的是什么对象（任意 Lean 定理 vs 抽出的合约语义）；ProofForge 现有 inline proof / PreservationABI 能否在剥离后原样复用。
3. **Lean 4 编译/抽取/FFI** — Lean 能否先编到汇编再交给外部工具；FFI 是“Lean 调原生”还是“Lean 编成链上二进制”；lake/compiler backend 实际产出是什么。
4. **Solana/sBPF 物化路径** — ProofForge 已有 Plan → HandlerIR → `.s` → locked `sbpf` → `.so`；SVM 账户模型、CPI、无 GC/无运行时对“普通 Lean”的硬约束。
5. **剥离成本与耦合** — Solana materializer 对 SemanticProgramV1 / CheckV1 / Normalize / capability 的依赖面；独立仓最小闭环要带走什么。
6. **对照方案与失败模式** — 同类工作（Lean→C/LLVM、Rust/Anchor、Certora、sBPF semantics provider）；“看起来能编、语义对不上”的失败点。

## Completion criteria

- [ ] 每个维度至少从代码/文档/官方资料两边交叉验证
- [ ] 明确区分：可行 / 有条件可行 / 不可行，并写出不可行的根因（不是口号）
- [ ] 画出若做独立 `proofforge` 的最小架构与明确不做的事
- [ ] 关键断言有验证记录（读源码、读官方文档、必要时跑命令）
- [ ] Verifier 在 min_rounds 后 PASS

## Scope

- In: ProofForge 语言/编译/Solana 后端事实；Lean 4 编译器、FFI、extraction；Solana sBPF/SVM 部署约束；独立仓可行性与推荐路径
- Out: 不在本轮实现编译器；不评估 EVM/NEAR 等其它 target 的剥离；不改 ProofForge 产品范围；不声称 formal TASK 完成
