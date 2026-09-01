---
id: svm-sdk-002
track: C-sdk
status: done
plan: ../svm-work-plan.md
priority: F1
---

# svm-sdk-002 owner-reassign 生命周期政策

## 目标

对 program-owned account 的 owner 再赋值：要么提供 checked facade，要么在能力矩阵标 `n/a` 并永久 fail closed——禁止半开。

## 决策

**永久 fail-closed / 能力矩阵 `n/a`。** Solana System `Assign` 只对 **system-owned** 账户生效；已 program-owned 账户的生命周期出口是 `Handle.closeTo`（resize-to-zero + 全额 refund），可选再走 System create/assign。不提供 `Handle.reassignOwner` / 任意 owner CPI——禁止半开。

## 交付

1. 书面政策：`ProofForge/Svm/Sdk/Account.lean` + `System.assign` 入站注释
2. 显式拒绝测试：
   - Lean：`Tests/OwnerReassignPolicySpec.lean`（禁止 facade 名；保留 closeTo / inbound assign）
   - Mollusk：`sys_alloc::assign_foreign_owned_fails_closed`（`ModifiedProgramId`，owner 不变）

## 非目标

任意账户类型的静默 owner 修改；实现半开的 owner 变更 facade。
