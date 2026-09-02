---
id: svm-sem-142
track: E-l3
status: done
plan: ../svm-work-plan.md
rung: E∞-knife
depends-on: [svm-sem-141]
---

# svm-sem-142 L3/E∞ knife 137 — Loader account-19 signer/writable after skip chain

## Goal

After the nonadecuple skip lands on the account-19 dup marker, emit loads account-19 signer/writable.

## Deliverables

1. `account19FlagsInputMem / walkAccount19FlagsAfterSkipChain?` / matching `evalAbsAccount19…?` helpers
2. Theorems: walk verified, POS constants, walk ≡ absLoad
3. Spec `#guard`s in `Tests/SolanalibSpec.lean`

## Evidence

- `ProofForge/Svm/Solanalib.lean` E∞ knife 137 section
- Spec guards for account-19 flags after nonadecuple skip
- Regenerated via `scripts/regenerate_account19_knives.py --all`

## Still open after this knife

account-19 remaining field arc; full multi-account vectors; syscall/CPI/sysvar; ELF accept.
