---
id: svm-sdk-001
track: C-sdk
status: todo
plan: ../svm-work-plan.md
priority: F1
---

# svm-sdk-001 resize rent top-up 显式政策

## 目标

账户 data resize 后按 Rent sysvar 做 **显式** rent top-up / 豁免检查政策，组合已有 Rent 查询与 lamport mutation。

## 交付

1. Sdk facade（无新 Emit recipe）
2. 租金不足 fail closed；零金额路径仍校验
3. 双 consumer + Mollusk

## 非目标

隐式自动掏 payer；runtime geometry。
