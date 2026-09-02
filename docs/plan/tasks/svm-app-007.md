---
id: svm-app-007
track: D-app
status: done
plan: ../svm-work-plan.md
depends-on: [svm-app-006]
---

# svm-app-007 Phoenix CancelMultipleById Vec capacity 4→8

## 目标

继续 full Phoenix quality matrix：把 tag 11 `CancelMultipleOrdersByIdWithFreeFunds` 的
`BoundedVec CancelOrderParams` 容量从 **4 提到 8**；tag 10 withdraw 因 9-account 标量局部门槛保持容量 4，并补 Mollusk 八 id free-funds
正例与超容量拒绝。

## 交付

1. `Examples/PhoenixV1Profile.lean`：tag 11 capacity=8（嵌套 `length ≥ 2..8`）；tag 10 保持 capacity=4
2. Spec：tag 11 `maxDataLen==141`；tag 10 `maxDataLen==73`；ASM `jgt r2, 141` 与 `jgt r2, 73`
3. Mollusk：helper 接受 `len≤8`；八 bid free-funds 正例；`length=9` 超容量拒绝
4. digest 纪律；无 Phoenix 名进入 `ProofForge/Svm`

## Evidence

- Lean: tag 11 `BoundedVec CancelOrderParams 8`; tag 10 stays capacity 4
- Spec: tag 11 maxDataLen 141 + `jgt r2, 141`; tag 10 maxDataLen 73 + `jgt r2, 73`
- Mollusk: `official_raw_cancel_by_id_free_funds_cancels_eight_owned_bids_in_one_vec`
- Registry digest `72e24d00aee1781c`

## 仍未覆盖

tag-10 withdraw 容量 8（标量局部门槛）；满官方容量 Vec；tags 0–2 / 12–17 / admin 100+；
tag-3 完整 TIF/self-trade/eviction；Token-2022 withdraw；remaining-accounts。
