---
id: svm-sem-043
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-042]
---

# svm-sem-043 L3/E∞ knife 38 — Loader account-5 header/key after skip chain

## 目标

在 account-5 dup marker skip 齐备之后，覆盖 Emit 对 account-5 的 header/key：
`ldxb` marker 与 `ldxdw` header+8。同一 quintuple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account5MetaInputMem` / `walkAccount5MetaAfterSkipChain?` /
   `evalWalkAccount5MetaAfterSkipChainToStack?` / `evalAbsAccount5Meta?`
2. Theorems：`walkAccount5MetaAfterSkipChain_verified`、
   `evalWalkAccount5_after_skip_key_0x75`、
   `walkAccount5MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 38 section
- Spec guards for marker=`0xAF`/`0xff` and key=`0x75` vs abs loads

## 仍未覆盖

account-5 signer/writable/lamports/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
