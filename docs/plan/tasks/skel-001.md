---
id: skel-001
scope: skeleton
status: done
depends-on: []
---

# skel-001 Lake 骨架 + Counter 参考语义

## objective

本仓可 `lake build`；Counter 用普通 Lean 写出并带一条真定理；手写 IR 描述符存在。

## context

- docs/01-prd.md
- docs/03-technical-spec.md
- docs/05-test-spec.md

## path

- lean-toolchain
- lakefile.lean
- ProofForge.lean
- ProofForge/
- Examples/Counter.lean
- Tests/CounterSpec.lean
- README.md
- docs/**

## verification

`lake build` 成功；T-S0-01…09 以 `#guard` / `example` 形式被检查。
