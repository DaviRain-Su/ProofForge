---
id: svm-app-006
track: D-app
status: done
plan: ../svm-work-plan.md
depends-on: [svm-app-005]
---

# svm-app-006 Phoenix CancelMultipleById tag-10 four-id withdraw Mollusk

## 目标

补全 capacity-4 CancelMultiple 矩阵证据：在 `svm-app-005` free-funds 四 id 正例之上，
为 **tag 10**（claim/withdraw）补 Mollusk 四 owned bid 一 vec 正例，验证聚合 quote
release → token withdraw。

## 交付

1. Mollusk：`official_raw_cancel_by_id_withdraw_cancels_four_owned_bids_and_claims_quote`
   （wire 73 bytes；sequence bump；bid book clear；quote vault/trader atoms）
2. 无 Lean entry/ASM 变更 → PhoenixV1Profile digest 保持 `6c073c1dcdb31f6`

## Evidence

- `runtime-tests/solana/tests/phoenix_v1_profile.rs` four-id withdraw test
- Existing Spec maxDataLen 73 / `jgt r2, 73` pins unchanged

## 仍未覆盖

cap>4 / 满官方 Vec；tags 0–2 / 12–17 / admin 100+；tag-3 TIF/self-trade/eviction /
`match_limit>2` 正例；Token-2022 withdraw；remaining-accounts。
