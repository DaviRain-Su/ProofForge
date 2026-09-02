---
id: svm-sem-039
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-038]
---

# svm-sem-039 L3/E∞ knife 34 — Loader account-4 owner limbs 0/1 after skip chain

## 目标

在 account-4 lamports/data_len 齐备之后，覆盖 Emit 对 account-4 的 owner 低 limbs：
`ldxdw` header+0x28 与 header+0x30。同一 quadruple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account4OwnerInputMem` / `walkAccount4OwnerAfterSkipChain?` /
   `evalWalkAccount4OwnerAfterSkipChainToStack?` / `evalAbsAccount4Owner?`
2. Theorems：`walkAccount4OwnerAfterSkipChain_verified`、
   `evalWalkAccount4_after_skip_owner0_0xE7_owner1_0xF8`、
   `walkAccount4OwnerAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 34 section
- Spec guards for owner0=0xE7 / owner1=0xF8 vs abs loads

## 仍未覆盖

account-4 owner limbs 2/3/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
