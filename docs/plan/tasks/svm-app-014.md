---
id: svm-app-014
track: D-app
status: doing
plan: ../svm-work-plan.md
depends-on: [svm-app-013]
---

# svm-app-014 Phoenix WithdrawFunds tag 12 (`Option<u64>` withdraw-all)

## 目标

CancelMultiple capacity is already at official tag-11/tag-10 cap 8. Next Phoenix quality-matrix
slice: replace the exact-lots WithdrawFunds wire with official Borsh
`Option<u64> × Option<u64>` so `None` withdraws that side's entire free balance (`Some(n)` keeps
exact lots; both-`None` withdraws all free quote+base).

## 交付

1. `Examples/Svm/PhoenixV1Profile.lean`：`withdrawFunds` → `@[pf_svm_raw_borsh_options 12 9 0 0 [8, 8]]`
2. Spec：adapter min/max wire routes；ASM presence discriminants；CPI metas unchanged
3. Mollusk：`None/None` drains free；`Some/Some` exact；mixed；zero-free header-only
4. digest 纪律；无 Phoenix 名进入 `ProofForge/Svm`

## Evidence

- (pending) Lean extract/emit digest
- (pending) Mollusk Option matrix

## 仍未覆盖

`Option` DepositFunds；tags 0–2 / 14–17 / admin 100+；tag-3 完整 TIF/self-trade/eviction。
