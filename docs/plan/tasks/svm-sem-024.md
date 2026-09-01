---
id: svm-sem-024
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-023]
---

# svm-sem-024 L3/E∞ knife 19 — Loader account-2 lamports/data_len after skip chain

## 目标

在 account-2 signer/writable 齐备之后，覆盖 Emit 对 account-2 的 lamports/data_len
预算字：header-relative `+0x48` / `+0x50`。同一 skip chain 推进的 `r2` 游标加载，并与
绝对 `r6`-相对加载一致。

## 交付

1. `account2BudgetInputMem` / `walkAccount2BudgetAfterSkipChain?` /
   `evalWalkAccount2BudgetAfterSkipChainToStack?` / `evalAbsAccount2Budget?`
2. Theorems：`walkAccount2BudgetAfterSkipChain_verified`、
   `evalWalkAccount2_after_skip_lamports_2000_dataLen_64`、
   `walkAccount2BudgetAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 19 section
- Spec guards for lamports=`2000` / data_len=`64` vs abs loads

## 仍未覆盖

account-2 owner/executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
