# 00 商业 / 立项验证

## 一句话

做一个 **Lean 的 Solana 编译剖面**，不是一门新合约语言。

## 为什么值得做

- Lean 4 本身就是可执行语言 + 证明器。正路是：用户写普通 `def` / `theorem`，编译器只补 SVM 缺的那一层。
- ProofForge 已经证明「受限合约 → HandlerIR → `.s` → `sbpf` → Mollusk 可跑 `.so`」这条工程链成立（StateCell 5/5）。
- 缺的是前端：今天 PF 用自定义 `program … where`。本仓走普通 Lean 表面，证明主语和编译主语是同一个 `def`（或抽出后同一 IR hash）。

## 不值得做的替代

- 再造一门 DSL 再证 DSL（PF 已做，不是本仓目标）。
- Lean FFI / 宿主 C / LLVM 直接出 sBPF（runtime 非法，调研已否决）。
- 承诺 v0 证明已部署 `.so`（缺 refinement 链）。

## 手动流程（已走通一次）

1. 在 PF 里用 DSL 写 StateCell。
2. 编到 `.s` / `.so`。
3. Mollusk 执行：init / increment / get / overflow 保持。
4. 相邻 Lean 定理钉在 `SemanticProgramV1` 上，不钉 `.so`。

本仓要把第 1 步换成普通 Lean `def`，第 2–3 步尽量复用，第 4 步改钉用户函数。

## 转向实现的标准

调研结论已写进 [research/03-feasibility.md](research/03-feasibility.md)。用户已拍板：在本仓按「正路」做。
