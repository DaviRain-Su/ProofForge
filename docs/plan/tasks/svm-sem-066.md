---
id: svm-sem-066
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-065]
---

# svm-sem-066 L3/E∞ knife 61 — Loader account-8 lamports/data_len after skip chain

## 目标

在 account-8 signer/writable 齐备之后，覆盖 Emit 对 account-8 lamports/data_len：
`ldxb`/`ldxdw` 相对 header 游标字段。同一 octuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account8BudgetInputMem` / `walkAccount8BudgetAfterSkipChain?` /
   `evalWalkAccount8BudgetAfterSkipChainToStack?` / `evalAbsAccount8Budget?`
2. Theorems：`walkAccount8BudgetAfterSkipChain_verified`、
   `evalWalkAccount8_after_skip_lamports_8000_dataLen_176`、
   `walkAccount8BudgetAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 61 section
- Spec guards for lamports=8000 / dataLen=176 vs abs loads

## 仍未覆盖

account-8 owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
