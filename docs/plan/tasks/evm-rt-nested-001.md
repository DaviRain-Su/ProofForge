---
id: evm-rt-nested-001
scope: evm
status: partial
depends-on: []
plan: ../multi-target-strategy.md
updated: 2026-09-02
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
| Tagged / Option/enum elements inside dynamic arrays | **✓** | `echoBoundedOptions` → `(bool,uint64)[]`; `echoBoundedEnums` → `(uint8,uint64,uint64)[]`; one-limb Option; Tagged Tuple v1 enums |
| Frames > `maxBoundedArrayLocalWords` (64) | fail-closed | resource ceiling |

## Progress (2026-09-02)

- **Ceiling landed**: `maxProductNesting = 2` + `Tests/CoreCodecSpec.lean`
- **Wide returns**: `echoBoundedWide` (`uint128[]`) — Extract limb expansion, Codec
  `sourceLimbWords`, Emit pack, IR rewrite for limb `indexGet`
- **Constructed returns**: `echoBoundedPairs` (`(uint64,uint16)[]`) — same pipeline
- Spec coverage: `Tests/EvmBoundedSpec.lean`, `Tests/CoreCodecSpec.lean`
- **Anvil OK/reject matrix** for wide/constructed: `runtime-tests/evm/anvil_bounded.sh`
  (`echoBoundedWide`, `echoBoundedPairs`, malformed/over-capacity calldata)
- **Aggregate storage slice**: `Storage.Static.nestedRecord` (Feature A depth ≤ 2) +
  `Examples.Evm.EvmAggregateStorage` (digest `f66d438ad668929d`) — nested `Bundle` State,
  leaf views, flat product (`bundleSignal`), and nested product views
  (`bundleView` → `(uint64,(uint8,bool))`, `detailsView` → `(uint8,bool)`); layout pinned by
  `Tests/EvmStaticStorageSpec`
- **Extract**: bare nested `Prod` returns flatten via `scalarResultValues` (was fail-closed
  `pair return` beyond one flat pair)
- **Anvil matrix** for aggregate storage: `runtime-tests/evm/anvil_aggregate_storage.sh`
  (`setBundle` / `setAmount`, leaf views, `bundleSignal` / `bundleView` / `detailsView`,
  Unauthorized non-admin)
- Constructed dynamic return from storage field trees: **landed** (`amountSidePairs` → `(uint64,uint8)[]`)
- **Tagged-in-array Option**: `echoBoundedOptions` (`BoundedVec (Option UInt64) 2` ↔ `(bool,uint64)[]`) —
  Codec wrap of Tagged Tuple v1 element plans + remapped `taggedGuards`, Extract 2-limb
  element expansion, Emit ABI JSON tuple[], Anvil OK/reject matrix
- **Tagged-in-array enum**: `echoBoundedEnums` (`BoundedVec TaggedSlot 2` ↔ `(uint8,uint64,uint64)[]`) —
  same wrap path for enum element plans; Extract tag+payload limbs; Anvil OK/reject matrix
- Still open: depth ceiling raise

## Non-goals

powdr backend; changing Profile shared lock without coordinator; unbounded recursion.

## Acceptance

P0 Feature A row in `multi-target-strategy.md` → wide/constructed Anvil + aggregate-storage Anvil
evidence landed; remaining open items are listed under Progress.
