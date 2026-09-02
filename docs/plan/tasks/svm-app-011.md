---
id: svm-app-011
track: D-app
status: done
plan: ../svm-work-plan.md
depends-on: [svm-app-010]
---

# svm-app-011 Phoenix CancelMultipleById tag-10 capacity 7→8

## 目标

在 tag 10 容量 7（max wire 124）之后，把 withdraw 路径的 `BoundedVec` 提到 **8**
（max wire 141，与 tag 11 对齐）。容量 8 在 seam 1152 下不够标量局部门槛；本片把缝
提到 **1216**（CPI 根 `r10-2240`），继续复用 `addReleasedAcc512At` densify。

## 交付

1. `ProofForge/Svm/Scratch.lean` + `Emit.lean`：scalar/CPI 缝 1152→1216
2. `Examples/PhoenixV1Profile.lean`：tag 10 capacity=8
3. Spec：tag 10 `maxDataLen==141`；ASM `jgt r2, 141`
4. Mollusk：八 id withdraw + reject len=9；digest `6bf08db0730bf300`

## Evidence

- Lean extract/emit ×3 稳定 → digest `6bf08db0730bf300`（max scalar local offset 1160 < 1216）
- Registry / Spec / Mollusk / Scratch guards 同步

## 仍未覆盖

其余 Phoenix 指令质量矩阵（非 CancelMultiple 容量轴）。
