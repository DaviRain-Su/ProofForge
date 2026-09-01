---
id: evm-rt-nested-001
scope: evm
status: partial
depends-on: []
plan: ../multi-target-strategy.md
updated: 2026-09-01
---

# evm-rt-nested-001 — nested / constructed / wide dynamic returns

## Context (Feature A)

Default product path remains Lean → Extract → Yul → locked solc. Codec requires explicit
dynamic ABI policy for bounded arrays/bytes/strings (`ProofForge/Evm/Codec.lean`).

## In-scope policy (Feature A ceiling)

| Shape | Status | Notes |
|---|---|---|
| Product nesting depth ≤ 2 | accepted | `maxProductNesting = 2` |
| Product nesting depth ≥ 3 | fail-closed | stable `evm/codec: product nesting depth …` |
| Top-level `BoundedVec` of **one-limb** scalars | accepted | R1-019 |
| Top-level `BoundedVec` of **wide one-ABI-word** scalars (`UInt128`/`UInt256`/`Addr20`/…) | accepted | Extract expands limbs; Emit packs ABI word |
| Top-level `BoundedVec` of **constructed static products** (one-limb leaves) | accepted | e.g. `(uint64,uint16)[]` |
| Nested dynamics (array-of-bytes, dynamic-in-tuple, …) | fail-closed | `staticAbiLeaves` / codec reject |
| Tagged / Option elements inside dynamic arrays | fail-closed | follow-up |
| Frames > `maxBoundedArrayLocalWords` (64) | fail-closed | resource ceiling |

## Progress (2026-09-01)

- **Ceiling landed**: `maxProductNesting = 2` + `Tests/CoreCodecSpec.lean`
- **Wide returns**: `echoBoundedWide` (`uint128[]`) — Extract limb expansion, Codec
  `sourceLimbWords`, Emit pack, IR rewrite for limb `indexGet`
- **Constructed returns**: `echoBoundedPairs` (`(uint64,uint16)[]`) — same pipeline
- Spec coverage: `Tests/EvmBoundedSpec.lean`, `Tests/CoreCodecSpec.lean`
- Still open: **Anvil OK/reject matrix** for wide/constructed; tagged-in-array; depth ceiling raise

## Non-goals

powdr backend; changing Profile shared lock without coordinator; unbounded recursion.

## Acceptance

P0 Feature A row in `multi-target-strategy.md` → done with Anvil evidence.
