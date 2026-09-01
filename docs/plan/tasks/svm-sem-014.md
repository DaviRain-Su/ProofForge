---
id: svm-sem-014
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-013]
---

# svm-sem-014 L3/E∞ knife 9 — Loader account-0 → next-account marker skip

## 目标

在 executable/rent_epoch 齐备之后，覆盖 Emit 对 account-0 的 skip 几何：
`r5 = header+88+data_len+MAX_PERMITTED_DATA_INCREASE`（零 data_len 时无 align 分支），
读 rent 后 `+8` 到达下一账户 dup marker（零 `EXACT_DATA_LEN` 布局下绝对 `0x2868`）。
同一 `r8` header 游标跳转，并与绝对 `r6`-相对加载一致。

## 交付

1. `account0SkipNextInputMem` / `walkAccount0SkipNext?` / `evalWalkAccount0SkipNextToStack?` /
   `evalAbsAccount1Marker?`
2. Theorems：`walkAccount0SkipNext_verified`、`evalWalkAccount0_skip_next_marker_0xff`、
   `walkAccount0SkipNext_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 9 section
- Spec guards for next marker=`0xff`/`0xAB` vs abs loads at `0x2868`

## 仍未覆盖

完整 multi-account 向量游标；syscall/CPI/sysvar；ELF accept。
