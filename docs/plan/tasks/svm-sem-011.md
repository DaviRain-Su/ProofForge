---
id: svm-sem-011
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-010]
---

# svm-sem-011 L3/E∞ knife 6 — Loader account-0 owner limbs

## 目标

在 `svm-sem-010` budget walk 之上，覆盖 Emit 对 account-0 的 `ACC0_OWNER` /
`ACC0_OWNER+8`：同一 `r8` header 游标 `ldxdw` 前两 owner 字，并与绝对 `r6`-相对加载一致。

## 交付

1. `account0OwnerInputMem` / `walkAccount0Owner?` / `evalWalkAccount0OwnerToStack?` /
   `evalAbsAccount0Owner?`
2. Theorems：`walkAccount0Owner_verified`、`evalWalkAccount0_owner0_0xA1_owner1_0xB2`、`walkAccount0Owner_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 6 section
- Spec guards for owner0=`0xA1` / owner1=`0xB2` vs abs loads

## 仍未覆盖

owner limbs 2–3；完整 account 向量；syscall/CPI/sysvar；ELF accept。
