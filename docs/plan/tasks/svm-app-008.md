---
id: svm-app-008
track: D-app
status: done
plan: ../svm-work-plan.md
depends-on: [svm-app-007]
---

# svm-app-008 Phoenix CancelMultipleById tag-10 capacity 4→5

## 目标

在 tag 11 已到容量 8 之后，推进 tag 10 withdraw 的 CancelMultiple 容量：在 9-account
标量局部门槛内把 `BoundedVec` 从 **4 提到 5**（max wire 90），并用 `pf_inline`
`finishCancelMultipleWithdraw512At` 压缩嵌套臂的 claim/withdraw 标量局部门槛。

容量 6/8 在当前 9-account 帧下仍触发 `extract/unsupported: too many scalar locals`。

## 交付

1. `Examples/PhoenixV1Profile.lean`：tag 10 capacity=5 + densified finish helper
2. Spec：tag 10 `maxDataLen==90`；ASM `jgt r2, 90`
3. Mollusk：五 id withdraw + reject len=6；digest `5fddbc7822acef7e`

## Evidence

- Lean extract ×3 稳定 → digest `5fddbc7822acef7e`（main Extract 合入后 densify `cancelOneReleased512At`）
- Registry / Spec / Mollusk 同步

## 仍未覆盖

tag 10 容量 6/8 / 满官方容量；其余 Phoenix 指令矩阵。
