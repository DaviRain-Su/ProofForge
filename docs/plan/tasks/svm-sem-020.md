---
id: svm-sem-020
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-019]
---

# svm-sem-020 L3/E∞ knife 15 — Loader account-1 executable/rent after skip

## 目标

在 account-1 owner limbs 0–3 齐备之后，覆盖 Emit 对 account-1 的 executable/rent_epoch
门控：`ldxb` header+3 与 zero-dataLen 布局的 `ldxdw` header+0x2858。同一 skip 推进的 `r2`
游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account1ExecRentInputMem` / `walkAccount1ExecRentAfterSkip?` /
   `evalWalkAccount1ExecRentAfterSkipToStack?` / `evalAbsAccount1ExecRent?`
2. Theorems：`walkAccount1ExecRentAfterSkip_verified`、
   `evalWalkAccount1_after_skip_executable_1_rent_0xEE`、
   `walkAccount1ExecRentAfterSkip_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 15 section
- Spec guards for executable=`1`/`0` and rent=`0xEE` vs abs loads

## 仍未覆盖

account-2 walk；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
