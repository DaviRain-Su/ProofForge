---
id: svm-sem-062
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-061]
---

# svm-sem-062 L3/E∞ knife 57 — Loader account-7 executable/rent after skip chain

## 目标

在 account-7 owner pubkey 齐备之后，覆盖 Emit 对 account-7 executable/rent：
`ldxb` header+3 与 `ldxdw` header+0x2858（zero-data layout）。同一 septuple skip chain
推进的 `r2` 游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account7ExecRentInputMem` / `walkAccount7ExecRentAfterSkipChain?` /
   `evalWalkAccount7ExecRentAfterSkipChainToStack?` / `evalAbsAccount7ExecRent?`
2. Theorems：`walkAccount7ExecRentAfterSkipChain_verified`、
   `evalWalkAccount7_after_skip_executable_1_rent_0xF2`、
   `walkAccount7ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 57 section
- Spec guards for executable=1 / rent=0xF2 vs abs loads

## 仍未覆盖

完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
