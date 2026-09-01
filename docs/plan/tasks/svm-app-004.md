---
id: svm-app-004
track: D-app
status: done
plan: ../svm-work-plan.md
depends-on: [svm-app-001]
---

# svm-app-004 Phoenix CancelMultipleById Vec capacity 1→2

## 目标

推进 full Phoenix quality matrix：把 tags 10/11 `CancelMultipleOrdersById*` 的
`BoundedVec CancelOrderParams` 容量从 **1 提到 2**，并补 Mollusk 双 id 正例。

## 交付

1. `Examples/PhoenixV1Profile.lean`：capacity=2；逐 id skip/cancel；非空 vec 仍一次
   sequence bump + batch；tag 10 聚合 quote/base release 后 claim/withdraw
2. Spec：`minDataLen==5`、`maxDataLen==39`（5 + 17×2）
3. Mollusk：`raw_cancel_by_id_data` 接受 `len≤2`；双 bid + mixed bid/ask free-funds 成功例
4. digest 纪律；无 Phoenix 名进入 `ProofForge/Svm`

## Evidence

- Lean entries tags 10/11 with `BoundedVec CancelOrderParams 2`
- `Tests/PhoenixV1ProfileSpec.lean` adapter maxDataLen 39
- `runtime-tests/solana/tests/phoenix_v1_profile.rs` dual-id + mixed bid/ask tests
- Registry digest `2dc1e143994eca61`

## 仍未覆盖

满官方容量 Vec；tags 0–2 / 12–17 / admin 100+；tag-3 完整 TIF/self-trade/eviction/
crossing remainder / `match_limit>2`；Token-2022 withdraw；remaining-accounts。
