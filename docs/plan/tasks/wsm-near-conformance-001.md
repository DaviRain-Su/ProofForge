---
id: wsm-near-conformance-001
scope: near
status: partial
depends-on: [wsm-near-ft-ledger-001]
plan: ../multi-target-strategy.md
updated: 2026-09-02
---

# wsm-near-conformance-001 — Counter/Token cross-target conformance (N15)

## Goal

Document and pin **shared semantic fixtures** that build on SVM, EVM, and NEAR from the
same Lean source, without pretending wire formats or storage geometry are identical.

## Landed (Counter first slice)

1. `Tests/CrossTargetCounterSpec` — authoritative three-target digest table for
   `Examples.Counter`:
   | Target | Registry digest |
   |---|---|
   | SVM | `3382e308fa0843e9` |
   | EVM | `254202356ee921d6` |
   | NEAR | `121a0c8f7e697642` |
2. Verifies shared entry surface (`initialize`, `increment`, `get`, …) across lowers
3. Reuses `#pf_near_build` / `#pf_evm_build` registry checks

## Landed (Token-shaped follow-up)

Token fixtures are **target-local** (no shared `Examples.Token` source yet).
`Tests/CrossTargetTokenSpec` pins the approve/transfer-shaped digest table and method
surfaces:

| Role | Fixture | Digest | Entry names |
|---|---|---|---|
| SVM approve | `Examples.Svm.TokenApprove` | `e99f2008d320e15c` | `approve`, `get`, `initialize` |
| SVM transfer | `Examples.Svm.TokenXfer` | `c9edc88528b425dd` | `send`, `get`, `initialize` |
| EVM approve/xfer | `Examples.EvmTokenErgonomics` | `138c08a82e1ad205` | `approve`, `transfer`, `transferFrom`, … |
| NEAR transfer | `Examples.Near.NearFungibleLedger` | `e1e290ddec221fa5` | `ft_transfer`, `ft_transfer_call`, … |

**Shared conceptual subset:** transfer-shaped on all three (names differ:
`send` / `transfer` / `ft_transfer`); approve-shaped on SVM+EVM only.

**Gaps (remaining N15):**
- No shared Lean source module for Token (unlike Counter)
- NEAR has no `approve` / allowance surface (NEP-141)
- SVM transfer entry is named `send`, not `transfer`
- Full EVM `Examples.Evm.Token` and NEAR `NearTokenErgonomics` arithmetic remain
  outside this approve/transfer digest table
- Optional CI lane label `conformance` (Lean gate already covers digests)

## Landed (runtime sandbox matrix pointers)

Token-shaped **engineering** gates (not shared digests) live at:

| Target | Fixture / role | Runtime gate |
|---|---|---|
| SVM approve | `Examples.Svm.TokenApprove` | `runtime-tests/solana/tests/token_approve.rs` (Mollusk) |
| SVM transfer | `Examples.Svm.TokenXfer` | `runtime-tests/solana/tests/token_xfer.rs` (Mollusk) |
| EVM Token (full) | `Examples.Evm.Token` | `runtime-tests/evm/anvil_token.sh` |
| EVM ergonomics | `Examples.EvmTokenErgonomics` | Lean `#pf_evm_build` via `Tests/CrossTargetTokenSpec` (no dedicated Anvil scene) |
| NEAR FT ledger | `Examples.Near.NearFungibleLedger` | `runtime-tests/near/ledger.sh` → `ledger.py` |
| NEAR FT events | companion | `runtime-tests/near/ft_event.sh` → `ft_event.py` |
| NEAR JSON FT inputs | companion | `runtime-tests/near/json_ft_transfer_input.sh`, `json_ft_transfer_call_input.sh` |

Lean digest authority remains `Tests/CrossTargetTokenSpec.lean` +
`Tests/CrossTargetCounterSpec.lean`. Runtime scripts are engineering gates only.

## Follow-up

- Optional shared `Examples.TokenShape` UInt64 stub if a true three-target source is needed
- Optional CI lane label `conformance` (currently covered by aggregate Lean gate)

## Non-goals

- Shared wire encoder or unified ABI
- XRPL (explicitly out of multi-target scope)

## Acceptance

N15 Counter row → **done** (digest table + method surface pinned).
N15 Token row → **partial** (target-local digest table + method surface + gaps documented +
runtime sandbox matrix pointers landed).
