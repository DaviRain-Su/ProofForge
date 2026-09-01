---
id: svm-sem-012
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-011]
---

# svm-sem-012 L3/E∞ knife 7 — Loader account-0 owner limbs 2/3

## 目标

在 `svm-sem-011` owner 前两 limb 之上，覆盖 Emit 对 account-0 的 `ACC0_OWNER+16` /
`ACC0_OWNER+24`：同一 `r8` header 游标 `ldxdw` 后两 owner 字，并与绝对 `r6`-相对加载一致。

## 交付

1. `account0OwnerHiInputMem` / `walkAccount0OwnerHi?` / `evalWalkAccount0OwnerHiToStack?` /
   `evalAbsAccount0OwnerHi?`
2. Theorems：`walkAccount0OwnerHi_verified`、`evalWalkAccount0_owner2_0xC3_owner3_0xD4`、
   `walkAccount0OwnerHi_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 7 section
- Spec guards for owner2=`0xC3` / owner3=`0xD4` vs abs loads

## 仍未覆盖

完整 account 向量；executable/rent_epoch（见 `svm-sem-013`）；syscall/CPI/sysvar；ELF accept。
