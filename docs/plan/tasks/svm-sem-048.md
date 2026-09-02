---
id: svm-sem-048
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-047]
---

# svm-sem-048 L3/E∞ knife 43 — Loader account-5 executable/rent after skip chain

## 目标

在 account-5 owner pubkey 齐备之后，覆盖 Emit 对 account-5 executable/rent_epoch：
`ldxb` header+3 与 `ldxdw` header+0x2858（zero-data layout）。同一 quintuple skip chain
推进的 `r2` 游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account5ExecRentInputMem` / `walkAccount5ExecRentAfterSkipChain?` /
   `evalWalkAccount5ExecRentAfterSkipChainToStack?` / `evalAbsAccount5ExecRent?`
2. Theorems：`walkAccount5ExecRentAfterSkipChain_verified`、
   `evalWalkAccount5_after_skip_executable_1_rent_0xF0`、
   `walkAccount5ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 43 section
- Spec guards for executable=1 / rent=0xF0 vs abs loads

## 仍未覆盖

account-6+ skip/field knives；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
