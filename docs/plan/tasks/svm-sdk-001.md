---
id: svm-sdk-001
track: C-sdk
status: done
plan: ../svm-work-plan.md
priority: F1
---

# svm-sdk-001 resize rent top-up 显式政策

## 目标

账户 data resize 后按 Rent sysvar 做 **显式** rent top-up / 豁免检查政策，组合已有 Rent 查询与 lamport mutation。

## 交付

1. Sdk facade（无新 Emit recipe） — `Handle.topUpRentExempt` / `Handle.resizeDataWithRentTopUp`
2. 租金不足 fail closed；零金额路径仍校验（saturating deficit → zero-amount transfer）
3. 双 consumer + Mollusk — `RentTopUp` (`389be3285e53c93d`) + `VaultRentGrow` (`754ab90d0d3145ae`)

## 非目标

隐式自动掏 payer；runtime geometry。

## 证据

- Lean: `ProofForge/Svm/Sdk/Account.lean`；`Tests/RentTopUpSpec.lean`；`Tests/VaultRentGrowSpec.lean`
- Mollusk: `runtime-tests/solana/tests/rent_top_up.rs` (4/4)；`vault_rent_grow.rs` (2/2)
- Extraction pitfall: discard effectful top-up with bare `let _ := resizeDataWithRentTopUp …` can DCE; bind deficit then resize.
