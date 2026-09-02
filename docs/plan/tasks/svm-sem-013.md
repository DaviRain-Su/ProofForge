---
id: svm-sem-013
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-012]
---

# svm-sem-013 L3/E∞ knife 8 — Loader account-0 executable + rent_epoch

## 目标

在 owner limbs 齐备之后，覆盖 Emit 对 account-0 的 `ACC0_HEADER+3`（executable）与
`.equ ACC0_RENT_EPOCH`（零 `EXACT_DATA_LEN` 布局下绝对 `0x2860`）：同一 `r8` header
游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account0ExecRentInputMem` / `walkAccount0ExecRent?` / `evalWalkAccount0ExecRentToStack?` /
   `evalAbsAccount0ExecRent?`
2. Theorems：`walkAccount0ExecRent_verified`、`evalWalkAccount0_executable_1_rent_0xEE`、
   `walkAccount0ExecRent_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 8 section
- Spec guards for executable=`1`/`0` and rent_epoch=`0xEE` vs abs loads

## 仍未覆盖

完整 account 向量；syscall/CPI/sysvar；ELF accept。
