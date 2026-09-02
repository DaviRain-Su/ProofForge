---
id: svm-sem-146
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-145]
---

# svm-sem-146 L3/E∞ knife 141 — Loader account-19 executable/rent_epoch after skip chain

## Goal

After the nonadecuple skip lands on the account-19 dup marker, emit loads account-19 executable/rent_epoch.

## Deliverables

1. `account19ExecRentInputMem / walkAccount19ExecRentAfterSkipChain?` / matching `evalAbsAccount19…?` helpers
2. Theorems: walk verified, POS constants, walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 141 section
- Spec guards for account-19 exec/rent after nonadecuple skip
- Regenerated via `scripts/regenerate_account19_knives.py --all`

## Still open after this knife

full multi-account vectors; syscall/CPI/sysvar; ELF accept.
