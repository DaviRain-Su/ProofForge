---
id: svm-sem-055
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-054]
---

# svm-sem-055 L3/E∞ knife 50 — Loader account-6 executable/rent after skip chain

## 目标

在 account-6 owner pubkey 齐备之后，覆盖 Emit 对 account-6 executable/rent_epoch：
`ldxb` header+3 与 `ldxdw` header+0x2858（zero-data layout）。同一 sextuple skip chain
推进的 `r2` 游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account6ExecRentInputMem` / `walkAccount6ExecRentAfterSkipChain?` /
   `evalWalkAccount6ExecRentAfterSkipChainToStack?` / `evalAbsAccount6ExecRent?`
2. Theorems：`walkAccount6ExecRentAfterSkipChain_verified`、
   `evalWalkAccount6_after_skip_executable_1_rent_0xF1`、
   `walkAccount6ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 50 section
- Spec guards for executable=1 / rent=0xF1 vs abs loads

## 仍未覆盖

完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
