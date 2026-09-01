---
id: svm-sem-015
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-014]
---

# svm-sem-015 L3/E∞ knife 10 — Loader account-1 header/key after skip

## 目标

在 account-0 → next-marker skip（`0x2868`）齐备之后，把 Emit 对下一账户的 header
游标当作 account-1：dup marker + 首个 key limb（`+8` → `0x2870`）。同一 skip 推进的
`r2` 游标加载，并与绝对 `r6`-相对加载一致。

## 交付

1. `account1MetaInputMem` / `walkAccount1MetaAfterSkip?` /
   `evalWalkAccount1MetaAfterSkipToStack?` / `evalAbsAccount1Meta?`
2. Theorems：`walkAccount1MetaAfterSkip_verified`、`evalWalkAccount1_after_skip_key_0x71`、
   `walkAccount1MetaAfterSkip_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 10 section
- Spec guards for marker=`0xff`/`0xAB` + key=`0x71` vs abs loads at `0x2868`/`0x2870`

## 仍未覆盖

完整 multi-account 向量；account-1 flags/lamports/owner/rent；syscall/CPI/sysvar；ELF accept。
