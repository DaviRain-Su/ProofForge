---
id: svm-sem-057
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-056]
---

# svm-sem-057 L3/E∞ knife 52 — Loader account-7 header/key after skip chain

## 目标

在 account-7 skip chain 齐备之后，覆盖 Emit 对 account-7 header/key：
`ldxb` marker 与 `ldxdw` header+8 key。同一 septuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account7MetaInputMem` / `walkAccount7MetaAfterSkipChain?` /
   `evalWalkAccount7MetaAfterSkipChainToStack?` / `evalAbsAccount7Meta?`
2. Theorems：`walkAccount7MetaAfterSkipChain_verified`、
   `evalWalkAccount7_after_skip_key_0x77`、
   `walkAccount7MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 52 section
- Spec guards for key=0x77 / marker=0xB3 vs abs loads

## 仍未覆盖

account-7 flags/budget/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
