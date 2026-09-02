---
id: svm-sem-052
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-051]
---

# svm-sem-052 L3/E∞ knife 47 — Loader account-6 lamports/data_len after skip chain

## 目标

在 account-6 signer/writable 齐备之后，覆盖 Emit 对 account-6 的 lamports/data_len：
`ldxdw` header+0x48 与 header+0x50。同一 sextuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account6BudgetInputMem` / `walkAccount6BudgetAfterSkipChain?` /
   `evalWalkAccount6BudgetAfterSkipChainToStack?` / `evalAbsAccount6Budget?`
2. Theorems：`walkAccount6BudgetAfterSkipChain_verified`、
   `evalWalkAccount6_after_skip_lamports_6000_dataLen_144`、
   `walkAccount6BudgetAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 47 section
- Spec guards for lamports=6000 / data_len=144 vs abs loads

## 仍未覆盖

account-6 owner limbs/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
