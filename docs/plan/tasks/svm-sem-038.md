---
id: svm-sem-038
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-037]
---

# svm-sem-038 L3/E∞ knife 33 — Loader account-4 lamports/data_len after skip chain

## 目标

在 account-4 signer/writable 齐备之后，覆盖 Emit 对 account-4 的 lamports/data_len：
`ldxdw` header+0x48 与 header+0x50。同一 quadruple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account4BudgetInputMem` / `walkAccount4BudgetAfterSkipChain?` /
   `evalWalkAccount4BudgetAfterSkipChainToStack?` / `evalAbsAccount4Budget?`
2. Theorems：`walkAccount4BudgetAfterSkipChain_verified`、
   `evalWalkAccount4_after_skip_lamports_4000_dataLen_112`、
   `walkAccount4BudgetAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 33 section
- Spec guards for lamports=4000 / data_len=112 vs abs loads

## 仍未覆盖

account-4 owner limbs/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
