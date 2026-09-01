---
id: svm-sem-076
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-075]
---

# svm-sem-076 L3/E∞ knife 71 — Loader account-9 executable/rent after skip chain

## 目标

在 account-9 owner pubkey 齐备之后，覆盖 Emit 对 account-9 executable/rent：
`ldxb`/`ldxdw` 相对 header 游标字段。同一 nonuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account9ExecRentInputMem` / `walkAccount9ExecRentAfterSkipChain?` /
   `evalWalkAccount9ExecRentAfterSkipChainToStack?` / `evalAbsAccount9ExecRent?`
2. Theorems：`walkAccount9ExecRentAfterSkipChain_verified`、
   `evalWalkAccount9_after_skip_executable_1_rent_0xF4`、
   `walkAccount9ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 71 section
- Spec guards for executable=1 / rent=0xF4 vs abs loads

## 仍未覆盖

完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
