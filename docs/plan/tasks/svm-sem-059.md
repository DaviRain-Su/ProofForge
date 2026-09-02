---
id: svm-sem-059
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-058]
---

# svm-sem-059 L3/E∞ knife 54 — Loader account-7 lamports/data_len after skip chain

## 目标

在 account-7 signer/writable 齐备之后，覆盖 Emit 对 account-7 lamports/data_len：
`ldxdw` header+0x48 与 header+0x50。同一 septuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account7BudgetInputMem` / `walkAccount7BudgetAfterSkipChain?` /
   `evalWalkAccount7BudgetAfterSkipChainToStack?` / `evalAbsAccount7Budget?`
2. Theorems：`walkAccount7BudgetAfterSkipChain_verified`、
   `evalWalkAccount7_after_skip_lamports_7000_dataLen_160`、
   `walkAccount7BudgetAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 54 section
- Spec guards for lamports=7000 / data_len=160 vs abs loads

## 仍未覆盖

account-7 owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
