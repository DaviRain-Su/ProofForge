---
id: svm-app-015
track: D-app
status: done
plan: ../svm-work-plan.md
depends-on: [svm-app-014]
---

# svm-app-015 Phoenix DepositFunds tag 13 (`Option<u64>` deposit-all)

## 目标

Advance the Phoenix quality matrix past Option WithdrawFunds: replace the exact-lots
DepositFunds wire with official Borsh `Option<u64> × Option<u64>` so `None` deposits that
side's entire trader token balance floored to whole lots (`Some(n)` keeps exact lots;
both-`None` with empty balances is header-only).

## 交付

1. `Examples/Svm/PhoenixV1Profile.lean`：`depositFunds` → `@[pf_entry, pf_svm_raw_borsh_options 13 9 0 0 [8, 8]]` + `depositLotsFromTokenAt`
2. Spec：adapter min/max Option wire routes；CPI metas unchanged
3. Mollusk：`Some/Some` exact；`None/None` deposit-all floor；`Some(0)/Some(0)` header-only；underflow reject
4. digest 纪律；无 Phoenix 名进入 `ProofForge/Svm`

## Evidence

- Lean extract/emit digest `1049b9843a832a95`
- Mollusk: Some/Some credits, None/None deposit-all, zero/zero header-only, underflow reject

## 仍未覆盖

tags 0–2 / 15–17 / admin 100+；tag-3 完整 TIF/self-trade/eviction。RequestSeat tag 14 — see [svm-app-016](svm-app-016.md).
