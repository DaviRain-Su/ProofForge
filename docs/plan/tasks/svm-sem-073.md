---
id: svm-sem-073
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-072]
---

# svm-sem-073 L3/E∞ knife 68 — Loader account-9 lamports/data_len after skip chain

## 目标

在 account-9 signer/writable 齐备之后，覆盖 Emit 对 account-9 lamports/data_len：
`ldxdw` 相对 header 游标字段。同一 nonuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account9BudgetInputMem` / `walkAccount9BudgetAfterSkipChain?` /
   `evalWalkAccount9BudgetAfterSkipChainToStack?` / `evalAbsAccount9Budget?`
2. Theorems：`walkAccount9BudgetAfterSkipChain_verified`、
   `evalWalkAccount9_after_skip_lamports_9000_dataLen_192`、
   `walkAccount9BudgetAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 68 section
- Spec guards for lamports=9000 / dataLen=192 vs abs loads

## 仍未覆盖

account-9 owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
