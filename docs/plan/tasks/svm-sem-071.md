---
id: svm-sem-071
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-070]
---

# svm-sem-071 L3/E∞ knife 66 — Loader account-9 header/key after skip chain

## 目标

在 account-9 dup marker 齐备之后，覆盖 Emit 对 account-9 header/key：
`ldxb`/`ldxdw` 相对 header 游标字段。同一 nonuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account9MetaInputMem` / `walkAccount9MetaAfterSkipChain?` /
   `evalWalkAccount9MetaAfterSkipChainToStack?` / `evalAbsAccount9Meta?`
2. Theorems：`walkAccount9MetaAfterSkipChain_verified`、
   `evalWalkAccount9_after_skip_key_0x79`、
   `walkAccount9MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 66 section
- Spec guards for key=0x79 / marker=0xB6 vs abs loads

## 仍未覆盖

account-9 flags/budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
