---
id: svm-app-016
track: D-app
status: done
plan: ../svm-work-plan.md
depends-on: [svm-app-015]
---

# svm-app-016 Phoenix RequestSeat tag 14

## 目标

Advance the Phoenix quality matrix past Option DepositFunds: land official
`RequestSeat` tag 14 so a trader can create the `["seat", market, trader]` PDA,
receive an Approved 128-byte seat record, and register into the market-resident
128-seat trader tree (CancelMultiple remains at official cap 8).

## 交付

1. `Examples/Svm/PhoenixV1Profile.lean`：`requestSeat` → `@[pf_entry, pf_svm_raw 14 6 0]`
2. Spec：raw adapter tag/accounts/dataLen；PDA + System CPI + trader-tree insert composition
3. Mollusk：success creates Approved seat + trader; duplicate trader / pre-sized seat reject
4. digest 纪律；无 Phoenix 名进入 `ProofForge/Svm`

## Evidence

- Lean extract/emit digest `c50584a88d34bf4b`
- Mollusk: RequestSeat success + reject paths (in land)

## 仍未覆盖

tags 0–2 / 15–17 / admin 100+；tag-3 完整 TIF/self-trade/eviction。
