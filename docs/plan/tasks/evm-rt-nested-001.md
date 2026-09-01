---
id: evm-rt-nested-001
scope: evm
status: todo
depends-on: []
plan: ../multi-target-strategy.md
---

# evm-rt-nested-001 — nested / constructed / wide dynamic returns

## Context (Feature A)

Default product path remains Lean → Extract → Yul → locked solc. Codec today fail-closes
empty tuples and requires explicit dynamic ABI policy for bounded arrays/bytes/strings
(`ProofForge/Evm/Codec.lean`). Nested constructed returns and wide dynamic aggregates are
still outside the accepted surface.

## Deliverables

1. Policy: which nested shapes are in-scope (depth/width ceilings) vs fail-closed
2. Codec/Extract: accept the in-scope subset; reject the rest with stable `evm/codec:` errors
3. Anvil malformed matrix: nested OK cases + reject cases
4. No Feature B / powdr coupling

## Non-goals

powdr backend; changing Profile shared lock without coordinator; unbounded recursion.

## Acceptance

P0 Feature A row in `multi-target-strategy.md` → done with Anvil evidence.
