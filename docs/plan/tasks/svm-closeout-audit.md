---
id: svm-closeout-audit
track: F-eng
status: done
plan: ../svm-work-plan.md
---

# SVM Tracks A–F closeout audit

## Objective (original)

1. Refine SVM work-plan docs for implementation fidelity.
2. Implement planned SVM work from Phase 1 Queue formalization through
   `sf-*`, `svm-rt-*`, `svm-sdk-*`, `svm-app-*`, `svm-sem-*`, `svm-eng-*`
   as far as the plan defines, with commits/PRs and verified Lean builds.
3. Leave WASM PRs #4/#5 alone; do not redo Queue theorems already on main.

## Task ledger (front-matter)

| Track | Tasks | Status |
|---|---|---|
| A formalization | `sf-000`…`sf-016` | **all done** |
| B runtime | `svm-rt-001`…`005` | **all done** |
| C SDK | `svm-sdk-001`…`007` | **all done** |
| D app | `svm-app-001`…`003` | **all done** |
| E L3 | `svm-sem-001`…`005` | **all done** |
| F eng | `svm-eng-001`…`002` | **all done** |

Post-closeout knives (outside original A–F ledger, still on this PR):
`svm-app-004` (CancelMultiple cap 1→2 + mixed bid/ask), `svm-sem-006`/`007` (E∞ walked `r7`).

Plan index/matrix rows scrubbed of leftover `todo` for these ids (2026-09-01 audit).

## Evidence spot-checks

- L2 Queue empty-push algebra in `ProofForge/Svm/Sdk/StorageModel.lean`
- L3 E1–E5 in `ProofForge/Svm/Solanalib.lean` (materialize, CFG, AccountWords↔storev, Queue empty-push)
- Registry digests for Counter / TicketLine / FeatureBits / VersionedLedger / PhoenixV1Profile
- Non-Phoenix mini-examples index: `docs/modules/sdk-mini-examples.md`
- Mollusk: ticket_line / storage_bit_set / storage_enumerable_set / versioned_codec green after rebuild
- Ownership gate script present; no WASM subjects in branch commits vs `main`

## Explicit non-claims

- Agave/ELF host adequacy (E∞) — **first knife** `svm-sem-006` walked `r7` (Loader/syscall/ELF still open)
- Full Phoenix instruction matrix beyond bounded tag-3..11 slices — **app-004** raises CancelMultiple cap 1→2 (rest still open)
- WASM workstreams (#4/#5 untouched)
- Re-proving main’s Queue nowrap-push / pop-clear theorems

## Verdict

Tracks A–F as defined by the current plan task ledger are **complete** under the
objective’s scope. Remaining work is backlog outside this ledger (E∞, full Phoenix,
optional Surfpool deploys).
