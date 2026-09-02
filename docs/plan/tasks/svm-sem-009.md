---
id: svm-sem-009
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-008]
---

# svm-sem-009 L3/E∞ knife 4 — Loader account-0 signer/writable flags

## 目标

在 `svm-sem-008` account-0 header/key walk 之上，覆盖 Emit 对 account-0 的
`ACC0_HEADER+1`（signer）与 `+2`（writable）门控：同一 `r8` 游标 `ldxb` 两字节，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account0FlagsInputMem` / `walkAccount0Flags?` / `evalWalkAccount0FlagsToStack?` /
   `evalAbsAccount0Flags?`
2. Theorems：`walkAccount0Flags_verified`、`evalWalkAccount0_signer_writable_1`、
   `walkAccount0Flags_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 4 section
- Spec guards for signer=`1` / writable=`0|1` vs abs loads

## 仍未覆盖

owner / lamports / data_len；完整 account 向量 walk；syscall/CPI/sysvar；ELF accept。
