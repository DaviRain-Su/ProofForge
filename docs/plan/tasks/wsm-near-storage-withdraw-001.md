---
id: wsm-near-storage-withdraw-001
scope: wasm
status: done
depends-on: [wsm-near-json-storage-withdraw-input-001, wsm-near-storage-deposit-001]
---

# wsm-near-storage-withdraw-001 bounded zero-available storage withdrawal

## Objective

Compose the bounded optional-u128 input and mutating exact `StorageBalance` output into public-shaped
export `storage_withdraw` over the canonical `BAL2` registration map, without inventing an available
balance or claiming complete NEP-145 compatibility.

## Delivered

- The exact one-yocto guard runs before the one caller-key read. Missing or malformed registrations,
  malformed input, positive requested amounts, zero trusted price, and checked retained-cost
  multiplication overflow all panic without map, state, supply, log, or Promise effects.
- Missing/null amount and explicit zero return exact
  `{"total":"(caller.length + 64) × trustedPrice","available":"0"}` for a present exact-16
  registration. Short and 64-byte callers use their own key geometry; no fixed cost is guessed.
- Success does not write or remove the `BAL2` entry, change total supply, emit a log, or stage a
  native refund. The attached security yocto is retained, matching the stock withdrawal path.
- Structural tests pin the exact export spelling, payable/input/output policies, guard-before-read,
  checked u128 multiplication, one-read/no-map-write source effects, and absence of log/Promise.
  Real nearcore scenes pin exact output bytes, variable caller totals, retained yocto, rejection and
  rollback boundaries, and unchanged registration/storage/supply.

## Compatibility boundary

The accepted 279-byte JSON grammar rejects unknown or escaped keys and limits aggregate whitespace;
near-sdk serde is broader. ProofForge also reports variable caller-key retained costs rather than the
stock FT's single configured fixed cost. The operation's zero-available behavior and security-yocto
retention follow near-contract-standards, but these input/economic differences preclude a complete
NEP-145 ABI or policy claim.
