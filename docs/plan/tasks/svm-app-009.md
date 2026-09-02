---
id: svm-app-009
track: D-app
status: done
plan: ../svm-work-plan.md
depends-on: [svm-app-008]
---

# svm-app-009 Phoenix CancelMultipleById tag-10 capacity 5→6

## 目标

在 tag 10 容量 5（max wire 90）之后，把 withdraw 路径的 `BoundedVec` 提到 **6**
（max wire 107）。9-account 帧下原先在嵌套 join locals 处撞上 scalar/CPI 缝
（`too many scalar locals`）；本片把缝从 1024 提到 **1088**（CPI 根 `r10-2112`，
深区 lowWater 同步），并用 `addReleasedAcc512At` densify 侧向累加。

## 交付

1. `ProofForge/Svm/Scratch.lean` + `Emit.lean`：scalar/CPI 缝 1024→1088
2. `Examples/PhoenixV1Profile.lean`：tag 10 capacity=6 + `addReleasedAcc512At`
3. Spec：tag 10 `maxDataLen==107`；ASM `jgt r2, 107`
4. Mollusk：六 id withdraw + reject len=7；digest `b88c8a2247d2c28e`

## Evidence

- Lean extract ×3 稳定 → digest `b88c8a2247d2c28e`
- emit ×3 成功（max scalar local &lt; 1088）
- Registry / Spec / Mollusk / Scratch guards 同步

## 仍未覆盖

tag 10 容量 7/8 / 满官方容量；其余 Phoenix 指令矩阵。
