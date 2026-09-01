---
id: svm-sem-041
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-040]
---

# svm-sem-041 L3/E∞ knife 36 — Loader account-4 executable/rent after skip chain

## 目标

在 account-4 owner pubkey 齐备之后，覆盖 Emit 对 account-4 的 executable/rent_epoch：
`ldxb` header+3 与 `ldxdw` header+0x2858（zero-dataLen 布局）。同一 quadruple skip chain
推进的 `r2` 游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account4ExecRentInputMem` / `walkAccount4ExecRentAfterSkipChain?` /
   `evalWalkAccount4ExecRentAfterSkipChainToStack?` / `evalAbsAccount4ExecRent?`
2. Theorems：`walkAccount4ExecRentAfterSkipChain_verified`、
   `evalWalkAccount4_after_skip_executable_1_rent_0xEF`、
   `walkAccount4ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 36 section
- Spec guards for executable=1/rent=0xEF and abs-load case executable=0/rent=0xEF

## 仍未覆盖

account-4 → account-5 skip chain；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
