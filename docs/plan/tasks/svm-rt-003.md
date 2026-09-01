---
id: svm-rt-003
track: B-runtime
status: done
plan: ../svm-work-plan.md
priority: F1
---

# svm-rt-003 AccountView + direct mutation 的 alias-aware walk

## 目标

当 bounded remaining-account view 与 fixed-handle direct mutation 同时使用时，提供 alias/writable/owner 感知的变量 walk，避免错误别名写入。

## 交付

1. 明确 preflight 规则（dup marker、writable、owner、长度） — **done**
   - Prelude：`emitWalkAccountsVariableAliasing`（static 前缀 alias 解析 + 变量尾部允许指向前缀的 Loader-v3 重复项）
   - View select：`useWalkedHeaders` 时从 prelude 已解析的 `headerStack` 取 canonical header
2. 负例矩阵：alias、readonly、foreign owner、OOB — **done**
   - Mollusk `account_view_mutation` 6/6（成功 transfer+peek、readonly、same-canonical、variable-tail alias、view OOB）
3. 无 runtime 任意 geometry；无 persistent pointer — **done**

## 验收证据

- Lean：`lake build Examples.AccountViewMutation Tests.AccountViewMutationSpec`
- Digest：`fee09f06d0cc60d4`
- Mollusk：`account_view_mutation` 6/6
- View-only `AccountView` digest 保持不变（`useWalkedHeaders` 默认 false）

## 非目标

开放 runtime-selected account index API。
