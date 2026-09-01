---
id: svm-app-005
track: D-app
status: done
plan: ../svm-work-plan.md
depends-on: [svm-app-004]
---

# svm-app-005 Phoenix CancelMultipleById Vec capacity 2→4

## 目标

继续 full Phoenix quality matrix：把 tags 10/11 `CancelMultipleOrdersById*` 的
`BoundedVec CancelOrderParams` 容量从 **2 提到 4**，并补 Mollusk 四 id 正例与
超容量拒绝。

## 交付

1. `Examples/PhoenixV1Profile.lean`：capacity=4；length-gated 逐 id cancel（嵌套
   `length ≥ 2/3/4`，与 cap=2 同构、extract 可接受）；tag 10 沿途聚合 quote/base
   后 inline claim/withdraw（避免 Prod / 过深 helper 导致 extract 失败）
2. Spec：`minDataLen==5`、`maxDataLen==73`（5 + 17×4）；ASM `jgt r2, 73`
3. Mollusk：`raw_cancel_by_id_data` 接受 `len≤4` / wire `5..=73`；四 bid free-funds
   正例；`length=5` 超容量拒绝
4. digest 纪律；无 Phoenix 名进入 `ProofForge/Svm`

## Evidence

- Lean entries tags 10/11 with `BoundedVec CancelOrderParams 4`
- `Tests/PhoenixV1ProfileSpec.lean` adapter maxDataLen 73
- `runtime-tests/solana/tests/phoenix_v1_profile.rs`
  `official_raw_cancel_by_id_free_funds_cancels_four_owned_bids_in_one_vec`
- Registry digest `6c073c1dcdb31f6`

## 仍未覆盖

满官方容量 Vec（官方 wire 仍可更大）；tags 0–2 / 12–17 / admin 100+；tag-3 完整
TIF/self-trade/eviction/crossing remainder / `match_limit>2`；Token-2022 withdraw；
remaining-accounts。
