---
id: svm-sem-029
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-028]
---

# svm-sem-029 L3/E∞ knife 24 — Loader account-3 header/key after skip chain

## 目标

在 account-3 dup marker skip 齐备之后，覆盖 Emit 对 account-3 的 header/key：
`ldxb` marker 与 `ldxdw` header+8。同一 triple skip chain 推进的 `r2` 游标加载，
并与绝对 `r6`-相对加载一致。

## 交付

1. `account3MetaInputMem` / `walkAccount3MetaAfterSkipChain?` /
   `evalWalkAccount3MetaAfterSkipChainToStack?` / `evalAbsAccount3Meta?`
2. Theorems：`walkAccount3MetaAfterSkipChain_verified`、
   `evalWalkAccount3_after_skip_key_0x73`、
   `walkAccount3MetaAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 24 section
- Spec guards for marker=`0xAB`/`0xff` and key=`0x73` vs abs loads

## 仍未覆盖

account-3 signer/writable/lamports/owner/exec-rent；完整 multi-account 向量；syscall/CPI/sysvar；ELF accept。
