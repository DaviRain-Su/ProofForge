---
id: svm-sem-140
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-139]
---

# svm-sem-140 L3/E∞ knife 135 — Loader account-18 → account-19 skip chain

## Goal

Knife 134 completes account-18 executable/rent after the octodecuple skip. Emit then
chains one more zero-`dataLen` skip so the host cursor lands on the account-19 dup marker.

## Deliverables

1. `account19SkipNextInputMem` / `walkAccount19SkipNextAfterSkipChain?` / matching
   `evalAbsAccount19…?` helpers (nonadecuple skip geometry)
2. Theorems: walk verified, POS constants, walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`
4. Prefer regenerating from the account-18 knife set via a
   `scripts/regenerate_account19_knives.py` sibling (same pattern as
   `regenerate_account18_knives.py`)

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 135 section (`account18SkipNextInputMem` / `walkAccount18SkipNextAfterSkipChain?` / `evalAbsAccount19Marker?`)
- Spec `#guard`s in `Tests/SolanalibSpec.lean`
- Regenerator: `scripts/regenerate_account19_knives.py` (default skip-only; `--all` for field arc)

## Still open after this knife

account-19 field arc: **landed** as [svm-sem-141](svm-sem-141.md)–[146](svm-sem-146.md)
(header/key → exec/rent); full multi-account vectors; syscall/CPI/sysvar; ELF accept.

## Notes

Tracks A–F closeout does **not** require E∞ completion; this knife is backlog outside the
Phase-1 ledger but is the documented frontier after `svm-sem-139`.
