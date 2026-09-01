---
id: wsm-near-promise-json-u128-result-001
scope: wasm
status: done
depends-on: [wsm-near-promise-result-001, wsm-near-json-u128-input-001, wsm-near-promise-ft-on-transfer-001]
---

# wsm-near-promise-json-u128-result-001 — strict quoted-u128 Promise result

## Objective

Add the smallest reusable Promise-result codec prerequisite for the future FT resolver. This slice
does not reconcile balances, add resolver arguments, or export `ft_resolve_transfer` or
`ft_transfer_call`.

## Authoritative boundary

- Current near-contract-standards declares `ft_on_transfer` as `PromiseOrValue<U128>` and its
  resolver reads dependency index zero with a 41-byte bound, deserializes `U128`, and otherwise
  falls back to the full transfer amount.
- The near-sdk-rs serde path is broader than ProofForge's chosen policy: within the bound it accepts
  surrounding JSON whitespace, leading plus/zeros, and JSON escapes that decode to parseable
  decimal digits. ProofForge intentionally accepts only exact bytes `"0"` or
  `"[1-9][0-9]{0,38}"`. A future resolver therefore treats serde-valid noncanonical spellings as
  invalid and refunds the full amount; this slice does not claim semantic equivalence.
- The future private resolver owns the exact `promise_results_count() == 1` guard and fixed index
  zero. `ResultBuffer.quotedU128` consumes only the immediately active capacity-41 descriptor.

## Delivered

- Compiler-owned `QuotedU128Result` carries exact nearcore status, valid, low limb, and high limb.
  Status 1 plus exact canonical syntax and checked full-u128 multiply-by-ten decoding yields
  `valid = 1`; failed/not-ready, oversized, malformed UTF-8/JSON, noncanonical, or overflowing
  results yield valid and both limbs zero without trapping.
- The bounded read resets descriptor metadata every time, copies successful results only when at
  most 41 bytes, and never reads stale register bytes for failed or oversized results. Canonical
  lowering names all three decoder leaves and includes them in the target digest.
- Targeted IR/WAT pins one count guard, one index-zero `promise_result`, capacity 41, quote/digit and
  max-u128 overflow thresholds, and all valid/low/high selectors. The fixture callback is private,
  diagnostic, and not an FT resolver.
- near-sandbox 2.13.0 runs genuine child → callback chains for zero, `2^64`, `2^64+1`, max-u128,
  leading zero/plus/whitespace, wrong type, unquoted/empty/malformed/overflow/oversized bytes, and a
  failed child. A valid → invalid → valid sequence pins register/frame isolation.

## Next

Add the private resolver argument boundary and ledger reconciliation as a separate slice. It must
use the existing `BAL2` ledger, exact callback authentication/count policy, and an explicit full
refund fallback for every invalid result described above.
