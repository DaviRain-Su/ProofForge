---
id: svm-sem-034
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-033]
---

# svm-sem-034 L3/E∞ knife 29 — Loader account-3 executable/rent after skip chain

## 目标

在 account-3 owner limbs 0–3 齐备之后，覆盖 Emit 对 account-3 的 executable/rent_epoch：
`ldxb` header+3 与 zero-dataLen 布局的 `ldxdw` header+0x2858。同一 triple skip chain
推进的 `r2` 游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account3ExecRentInputMem` / `walkAccount3ExecRentAfterSkipChain?` /
   `evalWalkAccount3ExecRentAfterSkipChainToStack?` / `evalAbsAccount3ExecRent?`
2. Theorems：`walkAccount3ExecRentAfterSkipChain_verified`、
   `evalWalkAccount3_after_skip_executable_1_rent_0xEE`、
   `walkAccount3ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 29 section
- Spec guards for executable=`1`/`0` and rent=`0xEE` vs abs loads

## 仍未覆盖

account-3 → account-4 skip；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
