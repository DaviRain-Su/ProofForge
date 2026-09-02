---
id: svm-sem-091
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-090]
---

# svm-sem-091 L3/E∞ knife 86 — Loader account-11 → account-12 skip chain

## 目标

在 account-11 executable/rent 齐备之后，覆盖 Emit 从 account-11 header 游标链式
`emitSkipAccount` 到 account-12 dup marker。同一 duodecuple（12-read）skip chain 推进的 `r2` 游标
加载 marker，并与绝对 `r6`-相对加载一致。

## 交付

1. `account11SkipNextInputMem` / `walkAccount11SkipNextAfterSkipChain?` /
   `evalWalkAccount11SkipNextAfterSkipChainToStack?` / `evalAbsAccount12Marker?`
2. Theorems：`walkAccount11SkipNextAfterSkipChain_verified`、`evalWalkAccount11_skip_next_marker_0xff`、`walkAccount11SkipNextAfterSkipChain_eq_absLoad`
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 86 section
- Spec guards for marker=0xff / marker=0xBA vs abs loads

## 仍未覆盖

account-12 meta/field knives。
