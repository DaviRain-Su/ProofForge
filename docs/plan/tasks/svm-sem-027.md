---
id: svm-sem-027
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-026]
---

# svm-sem-027 L3/E∞ knife 22 — Loader account-2 executable/rent after skip chain

## 目标

在 account-2 owner limbs 0–3 齐备之后，覆盖 Emit 对 account-2 的 executable/rent_epoch：
`ldxb` header+3 与 zero-dataLen 布局的 `ldxdw` header+0x2858。同一 skip chain 推进的
`r2` 游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account2ExecRentInputMem` / `walkAccount2ExecRentAfterSkipChain?` /
   `evalWalkAccount2ExecRentAfterSkipChainToStack?` / `evalAbsAccount2ExecRent?`
2. Theorems：`walkAccount2ExecRentAfterSkipChain_verified`、
   `evalWalkAccount2_after_skip_executable_1_rent_0xEE`、
   `walkAccount2ExecRentAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 22 section
- Spec guards for executable=`1`/`0` and rent=`0xEE` vs abs loads

## 仍未覆盖

完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
