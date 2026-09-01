# SVM status matrix (capability + formalization + L3)

> Single declaration page for `svm-eng-002`. Authority dates from the task front-matter
> files under [`tasks/`](tasks/) and the Track A matrix in
> [`svm-formalization-plan.md`](svm-formalization-plan.md) §6. Refresh with
> `python3 scripts/svm_status_summary.py`. Synced with [`svm-work-plan.md`](svm-work-plan.md) §6.

## 1. How to read this page

| Column | Meaning |
|---|---|
| Track | A formalization · B runtime · C SDK · D app · E L3 · F eng |
| Status | `done` / `doing` / `todo` / `n/a` from task front-matter |
| Evidence | Digests, Mollusk, theorems, or explicit fail-closed policy |

WASM PRs #4 / #5 stay open and out of this matrix.

## 2. Track A — formalization (`sf-*`)

| ID | Slice | Status |
|---|---|---|
| SF-0 … SF-10 (`sf-000`…`sf-016`) | Queue/Vec/BitSet/Transient/Alloc/Map/Set/Tree geometry/FifoCancel/BatchRecorder/facade L1 + closeout | **all done** |

Optional thickenings (Tree reachability / inverse) do not block Track A closeout.

## 3. Track B — runtime (`svm-rt-*`)

| ID | Slice | Status | Evidence |
|---|---|---|---|
| [svm-rt-001](tasks/svm-rt-001.md) | Signed Clock timestamps | **done** | Lean + Mollusk; digest `19039a4899e65b6d` |
| [svm-rt-002](tasks/svm-rt-002.md) | Token-2022 MintCloseAuthority | **done** | digest `607b3786fb54eaee` |
| [svm-rt-003](tasks/svm-rt-003.md) | Alias-aware AccountView walk | **done** | digest `fee09f06d0cc60d4` |
| [svm-rt-004](tasks/svm-rt-004.md) | Bounded Instructions / sliced sysvar | **done** | digest `fa750f0ebf227df3` |
| [svm-rt-005](tasks/svm-rt-005.md) | Nested / wide dynamic return policy | **done** | digest `243ea72de353e8e3`; Mollusk wide U128 |

## 4. Track C — SDK (`svm-sdk-*`)

| ID | Slice | Status |
|---|---|---|
| [svm-sdk-001](tasks/svm-sdk-001.md) | Resize rent top-up | **done** |
| [svm-sdk-002](tasks/svm-sdk-002.md) | Owner-reassign | **done (n/a fail-closed)** |
| [svm-sdk-003](tasks/svm-sdk-003.md) | Generic POD transient shapes | **done** |
| [svm-sdk-004](tasks/svm-sdk-004.md) | Manifest-bounded transient handles | **done** |
| [svm-sdk-005](tasks/svm-sdk-005.md) | Token-2022 Sdk facade | **done** |
| [svm-sdk-006](tasks/svm-sdk-006.md) | UTF-8 Memo + migration payloads | **done** |
| [svm-sdk-007](tasks/svm-sdk-007.md) | Bounded insert/remove/iteration | **done** |

## 5. Track D — application (`svm-app-*`)

| ID | Slice | Status |
|---|---|---|
| [svm-app-001](tasks/svm-app-001.md) | Phoenix-v1 next instruction group | **done** — tags 10/11 CancelMultipleById (cap=1); digest `baf247ca608bdc85` |
| [svm-app-002](tasks/svm-app-002.md) | Matching / fee / remainder | todo |
| [svm-app-003](tasks/svm-app-003.md) | Non-Phoenix SDK reuse examples | todo |

## 6. Track E — L3 sBPF bridge (`svm-sem-*`)

| Rung | ID | Slice | Status |
|---|---|---|---|
| E0 | (baseline) | Checked arith / store / branch ↔ Solanalib | **done** |
| E1 | [svm-sem-001](tasks/svm-sem-001.md) | Operand materialization + straightline | **done** |
| E2 | [svm-sem-002](tasks/svm-sem-002.md) | `.s` golden ↔ sbpfSemantics | **done** |
| E3 | [svm-sem-003](tasks/svm-sem-003.md) | Bounded CFG end-to-end (Counter) | **done** — 3-block increment; 7+5 / max+1 |
| E4 | [svm-sem-004](tasks/svm-sem-004.md) | AccountWords ↔ typed `storev` | **done** — Counter value word |
| E5 | [svm-sem-005](tasks/svm-sem-005.md) | Queue empty-push L3 | **done** |
| E∞ | — | Loader-v3 + full host/ELF | **not a completion condition** |

## 7. Track F — engineering (`svm-eng-*`)

| ID | Slice | Status |
|---|---|---|
| [svm-eng-001](tasks/svm-eng-001.md) | Formalization gates in CI | **done** |
| [svm-eng-002](tasks/svm-eng-002.md) | This dual/triple matrix page | **done** |

## 8. Capability matrix cross-links

Descriptive runtime/SDK surface (not a promise list):

- [capability-matrix.md](capability-matrix.md) — source → owner → effect → fail-closed edge
- [mainstream-parity.md](mainstream-parity.md) — F0–F3 priorities
- [runtime-sdk-roadmap.md](runtime-sdk-roadmap.md) — R2/R3 ceiling

When a `svm-*` knife lands, update the matching capability row and this page in the same PR.

## 9. CI summary

Optional local / CI one-liner (prints counts by status):

```bash
python3 scripts/svm_status_summary.py
```

Lean formalization gates remain `scripts/check_no_sorry.py` + named lake targets from `svm-eng-001`.
