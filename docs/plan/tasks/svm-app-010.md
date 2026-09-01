---
id: svm-app-010
track: D-app
status: done
plan: ../svm-work-plan.md
depends-on: [svm-app-009]
---

# svm-app-010 Phoenix CancelMultipleById tag-10 capacity 6→7

## 目标

在 tag 10 容量 6（max wire 107）之后，把 withdraw 路径的 `BoundedVec` 提到 **7**
（max wire 124）。容量 7 在 seam 1088 下仍触发 `too many scalar locals`；本片把缝
提到 **1152**（CPI 根 `r10-2176`），继续复用 `addReleasedAcc512At` densify。

## 交付

1. `ProofForge/Svm/Scratch.lean` + `Emit.lean`：scalar/CPI 缝 1088→1152
2. `Examples/PhoenixV1Profile.lean`：tag 10 capacity=7
3. Spec：tag 10 `maxDataLen==124`；ASM `jgt r2, 124`
4. Mollusk：七 id withdraw + reject len=8；digest `31c33408a7d9dbf7`

## Evidence

- Lean extract/emit ×3 稳定 → digest `31c33408a7d9dbf7`（max scalar local offset 1104 < 1152）
- Registry / Spec / Mollusk / Scratch guards 同步

## 仍未覆盖

tag 10 容量 8 / 满官方容量；其余 Phoenix 指令矩阵。
