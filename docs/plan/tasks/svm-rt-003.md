---
id: svm-rt-003
track: B-runtime
status: todo
plan: ../svm-work-plan.md
priority: F1
---

# svm-rt-003 AccountView + direct mutation 的 alias-aware walk

## 目标

当 bounded remaining-account view 与 fixed-handle direct mutation 同时使用时，提供 alias/writable/owner 感知的变量 walk，避免错误别名写入。

## 交付

1. 明确 preflight 规则（dup marker、writable、owner、长度）
2. 负例矩阵：alias、readonly、foreign owner、OOB
3. 无 runtime 任意 geometry；无 persistent pointer

## 非目标

开放 runtime-selected account index API。
