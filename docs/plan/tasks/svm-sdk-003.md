---
id: svm-sdk-003
track: C-sdk
status: done
plan: ../svm-work-plan.md
priority: F1
depends-on: []
---

# svm-sdk-003 generic POD transient record shapes

## 目标

在 Record64 / Vector128 / Vector256 之后，增加下一组仍 allocation-free 的 POD transient 形状（例如更多 limb 组合或固定 schema record），复用现有 bump lifecycle。

## 交付

1. 仅 SDK 组合，无新 Runtime leaf — `Transient.VectorPubkey`（4-limb `Sdk.Pubkey` schema over Record64）
2. 双 slot 隔离保留 — `bounded` / `boundedAlt`
3. 双 consumer — `TransientPubkeyBatch`（reject-at-full, digest `8958053c8b1f52ac`）+ `TransientPubkeyRing`（clear-and-reuse, digest `106f41e98d4dcc9c`）；Mollusk `transient_pubkey_vector` 8/8
4. 形式化跟踪：复用现有 TransientModel / `sf-*` 容器轨；本片为 SDK surface

## 非目标

泛型任意 POD 反射；持久化到 account；>2 slot（见 svm-sdk-004）。

## 证据

- Lean: `ProofForge/Svm/Sdk/TransientWideVec.lean` (`VectorPubkey`); `Tests/SvmTransientPubkeyVectorSpec.lean`
- Mollusk: `runtime-tests/solana/tests/transient_pubkey_vector.rs`
