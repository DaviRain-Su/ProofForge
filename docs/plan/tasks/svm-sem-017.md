---
id: svm-sem-017
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-016]
---

# svm-sem-017 L3/E∞ knife 12 — Loader account-1 lamports/data_len after skip

## 目标

在 account-1 signer/writable（`0x2869`/`0x286a`）齐备之后，覆盖 Emit 对 account-1 的
lamports/data_len 预算字：header-relative `+0x48` / `+0x50`。同一 skip 推进的 `r2`
游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account1BudgetInputMem` / `walkAccount1BudgetAfterSkip?` /
   `evalWalkAccount1BudgetAfterSkipToStack?` / `evalAbsAccount1Budget?`
2. Theorems：`walkAccount1BudgetAfterSkip_verified`、
   `evalWalkAccount1_after_skip_lamports_1000_dataLen_128`、
   `walkAccount1BudgetAfterSkip_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 12 section
- Spec guards for lamports=`1000` / data_len=`128` vs abs loads

## 仍未覆盖

account-1 owner/executable/rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
