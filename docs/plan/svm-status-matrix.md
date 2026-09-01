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
| [svm-app-001](tasks/svm-app-001.md) | Phoenix-v1 next instruction group | **done** — tags 10/11 CancelMultipleById (cap=1; see app-004→2, app-005→4, app-007→8); digest `72e24d00aee1781c` |
| [svm-app-002](tasks/svm-app-002.md) | Matching / fee / remainder | **done** |
| [svm-app-004](tasks/svm-app-004.md) | Phoenix CancelMultipleById Vec capacity 1→2 | **done** — maxDataLen 39; Mollusk dual-id + mixed bid/ask |
| [svm-app-005](tasks/svm-app-005.md) | Phoenix CancelMultipleById Vec capacity 2→4 | **done** — maxDataLen 73; Mollusk four-id + reject len=5 |
| [svm-app-006](tasks/svm-app-006.md) | Phoenix CancelMultipleById tag-10 four-id withdraw | **done** — Mollusk aggregate quote claim |
| [svm-app-007](tasks/svm-app-007.md) | Phoenix CancelMultipleById tag-11 capacity 4→8 | **done** — tag11 maxDataLen 141; Mollusk eight-id free-funds + reject len=9 |
| [svm-app-008](tasks/svm-app-008.md) | Phoenix CancelMultipleById tag-10 capacity 4→5 | **done** — maxDataLen 90; digest `5fddbc7822acef7e`; Mollusk five-id + reject len=6 |
| [svm-app-009](tasks/svm-app-009.md) | Phoenix CancelMultipleById tag-10 capacity 5→6 | **done** — seam 1088; maxDataLen 107; digest `b88c8a2247d2c28e`; Mollusk six-id + reject len=7 |
| [svm-app-010](tasks/svm-app-010.md) | Phoenix CancelMultipleById tag-10 capacity 6→7 | **done** — seam 1152; maxDataLen 124; digest `31c33408a7d9dbf7`; Mollusk seven-id + reject len=8 |
| [svm-app-011](tasks/svm-app-011.md) | Phoenix CancelMultipleById tag-10 capacity 7→8 | **done** — seam 1216; maxDataLen 141; digest `6bf08db0730bf300`; Mollusk eight-id + reject len=9 |
| [svm-app-012](tasks/svm-app-012.md) | Phoenix WithdrawFunds tag 12 (exact-lots) | **done** — wire 17; digest `c67cc383aa680001`; Mollusk quote+base + zero/zero + insufficient |
| [svm-app-013](tasks/svm-app-013.md) | Phoenix DepositFunds tag 13 (exact-lots) | **done** — wire 17; digest `5e9097d41f7cefbf`; Mollusk quote+base + zero/zero + underflow |
| [svm-sem-006](tasks/svm-sem-006.md) | E∞ walked `r7` arg0 | **done** |
| [svm-sem-007](tasks/svm-sem-007.md) | E∞ two consecutive walked `r7` args | **done** |
| [svm-sem-008](tasks/svm-sem-008.md) | E∞ Loader account-0 header/key walk | **done** |
| [svm-sem-009](tasks/svm-sem-009.md) | E∞ Loader account-0 signer/writable flags | **done** |
| [svm-sem-010](tasks/svm-sem-010.md) | E∞ Loader account-0 lamports/data_len | **done** |
| [svm-sem-011](tasks/svm-sem-011.md) | E∞ Loader account-0 owner limbs 0/1 | **done** |
| [svm-sem-012](tasks/svm-sem-012.md) | E∞ Loader account-0 owner limbs 2/3 | **done** |
| [svm-sem-013](tasks/svm-sem-013.md) | E∞ Loader account-0 executable/rent_epoch | **done** |
| [svm-sem-014](tasks/svm-sem-014.md) | E∞ Loader account-0 → next-account marker skip | **done** |
| [svm-sem-015](tasks/svm-sem-015.md) | E∞ Loader account-1 header/key after skip | **done** |
| [svm-sem-016](tasks/svm-sem-016.md) | E∞ Loader account-1 signer/writable after skip | **done** |
| [svm-sem-017](tasks/svm-sem-017.md) | E∞ Loader account-1 lamports/data_len after skip | **done** |
| [svm-sem-018](tasks/svm-sem-018.md) | E∞ Loader account-1 owner limbs 0/1 after skip | **done** |
| [svm-sem-019](tasks/svm-sem-019.md) | E∞ Loader account-1 owner limbs 2/3 after skip | **done** |
| [svm-sem-020](tasks/svm-sem-020.md) | E∞ Loader account-1 executable/rent after skip | **done** |
| [svm-sem-021](tasks/svm-sem-021.md) | E∞ Loader account-1 → account-2 skip chain | **done** |
| [svm-sem-022](tasks/svm-sem-022.md) | E∞ Loader account-2 header/key after skip chain | **done** |
| [svm-sem-023](tasks/svm-sem-023.md) | E∞ Loader account-2 signer/writable after skip chain | **done** |
| [svm-sem-024](tasks/svm-sem-024.md) | E∞ Loader account-2 lamports/data_len after skip chain | **done** |
| [svm-sem-025](tasks/svm-sem-025.md) | E∞ Loader account-2 owner limbs 0/1 after skip chain | **done** |
| [svm-sem-026](tasks/svm-sem-026.md) | E∞ Loader account-2 owner limbs 2/3 after skip chain | **done** |
| [svm-sem-027](tasks/svm-sem-027.md) | E∞ Loader account-2 executable/rent after skip chain | **done** |
| [svm-sem-028](tasks/svm-sem-028.md) | E∞ Loader account-2 → account-3 skip chain | **done** |
| [svm-sem-029](tasks/svm-sem-029.md) | E∞ Loader account-3 header/key after skip chain | **done** |
| [svm-sem-030](tasks/svm-sem-030.md) | E∞ Loader account-3 signer/writable after skip chain | **done** |
| [svm-sem-031](tasks/svm-sem-031.md) | E∞ Loader account-3 lamports/data_len after skip chain | **done** |
| [svm-sem-032](tasks/svm-sem-032.md) | E∞ Loader account-3 owner limbs 0/1 after skip chain | **done** |
| [svm-sem-033](tasks/svm-sem-033.md) | E∞ Loader account-3 owner limbs 2/3 after skip chain | **done** |
| [svm-sem-034](tasks/svm-sem-034.md) | E∞ Loader account-3 executable/rent after skip chain | **done** |
| [svm-sem-035](tasks/svm-sem-035.md) | E∞ Loader account-3 → account-4 skip chain | **done** |
| [svm-sem-036](tasks/svm-sem-036.md) | E∞ Loader account-4 header/key after skip chain | **done** |
| [svm-sem-037](tasks/svm-sem-037.md) | E∞ Loader account-4 signer/writable after skip chain | **done** |
| [svm-sem-038](tasks/svm-sem-038.md) | E∞ Loader account-4 lamports/data_len after skip chain | **done** |
| [svm-sem-039](tasks/svm-sem-039.md) | E∞ Loader account-4 owner limbs 0/1 after skip chain | **done** |
| [svm-sem-040](tasks/svm-sem-040.md) | E∞ Loader account-4 owner limbs 2/3 after skip chain | **done** |
| [svm-sem-041](tasks/svm-sem-041.md) | E∞ Loader account-4 executable/rent after skip chain | **done** |
| [svm-sem-042](tasks/svm-sem-042.md) | E∞ Loader account-4 → account-5 skip chain | **done** |
| [svm-sem-043](tasks/svm-sem-043.md) | E∞ Loader account-5 header/key after skip chain | **done** |
| [svm-sem-044](tasks/svm-sem-044.md) | E∞ Loader account-5 signer/writable after skip chain | **done** |
| [svm-sem-045](tasks/svm-sem-045.md) | E∞ Loader account-5 lamports/data_len after skip chain | **done** |
| [svm-sem-046](tasks/svm-sem-046.md) | E∞ Loader account-5 owner limbs 0/1 after skip chain | **done** |
| [svm-sem-047](tasks/svm-sem-047.md) | E∞ Loader account-5 owner limbs 2/3 after skip chain | **done** |
| [svm-sem-048](tasks/svm-sem-048.md) | E∞ Loader account-5 executable/rent after skip chain | **done** |
| [svm-sem-049](tasks/svm-sem-049.md) | E∞ Loader account-5 → account-6 skip chain | **done** |
| [svm-sem-050](tasks/svm-sem-050.md) | E∞ Loader account-6 header/key after skip chain | **done** |
| [svm-sem-051](tasks/svm-sem-051.md) | E∞ Loader account-6 signer/writable after skip chain | **done** |
| [svm-sem-052](tasks/svm-sem-052.md) | E∞ Loader account-6 lamports/data_len after skip chain | **done** |
| [svm-sem-053](tasks/svm-sem-053.md) | E∞ Loader account-6 owner limbs 0/1 after skip chain | **done** |
| [svm-sem-054](tasks/svm-sem-054.md) | E∞ Loader account-6 owner limbs 2/3 after skip chain | **done** |
| [svm-sem-055](tasks/svm-sem-055.md) | E∞ Loader account-6 executable/rent after skip chain | **done** |
| [svm-sem-056](tasks/svm-sem-056.md) | E∞ Loader account-6 → account-7 skip chain | **done** |
| [svm-sem-057](tasks/svm-sem-057.md) | E∞ Loader account-7 header/key after skip chain | **done** |
| [svm-sem-058](tasks/svm-sem-058.md) | E∞ Loader account-7 signer/writable after skip chain | **done** |
| [svm-sem-059](tasks/svm-sem-059.md) | E∞ Loader account-7 lamports/data_len after skip chain | **done** |
| [svm-sem-060](tasks/svm-sem-060.md) | E∞ Loader account-7 owner limbs 0/1 after skip chain | **done** |
| [svm-sem-061](tasks/svm-sem-061.md) | E∞ Loader account-7 owner limbs 2/3 after skip chain | **done** |
| [svm-sem-062](tasks/svm-sem-062.md) | E∞ Loader account-7 executable/rent after skip chain | **done** |
| [svm-sem-063](tasks/svm-sem-063.md) | E∞ Loader account-7 → account-8 skip chain | **done** |
| [svm-sem-064](tasks/svm-sem-064.md) | E∞ Loader account-8 header/key after skip chain | **done** |
| [svm-sem-065](tasks/svm-sem-065.md) | E∞ Loader account-8 signer/writable after skip chain | **done** |
| [svm-sem-066](tasks/svm-sem-066.md) | E∞ Loader account-8 lamports/data_len after skip chain | **done** |
| [svm-sem-067](tasks/svm-sem-067.md) | E∞ Loader account-8 owner limbs 0/1 after skip chain | **done** |
| [svm-sem-068](tasks/svm-sem-068.md) | E∞ Loader account-8 owner limbs 2/3 after skip chain | **done** |
| [svm-sem-069](tasks/svm-sem-069.md) | E∞ Loader account-8 executable/rent after skip chain | **done** |
| [svm-sem-070](tasks/svm-sem-070.md) | E∞ Loader account-8 → account-9 skip chain | **done** |
| [svm-sem-071](tasks/svm-sem-071.md) | E∞ Loader account-9 header/key after skip chain | **done** |
| [svm-sem-072](tasks/svm-sem-072.md) | E∞ Loader account-9 signer/writable after skip chain | **done** |
| [svm-sem-073](tasks/svm-sem-073.md) | E∞ Loader account-9 lamports/data_len after skip chain | **done** |
| [svm-sem-074](tasks/svm-sem-074.md) | E∞ Loader account-9 owner limbs 0/1 after skip chain | **done** |
| [svm-sem-075](tasks/svm-sem-075.md) | E∞ Loader account-9 owner limbs 2/3 after skip chain | **done** |
| [svm-sem-076](tasks/svm-sem-076.md) | E∞ Loader account-9 executable/rent after skip chain | **done** |
| [svm-sem-077](tasks/svm-sem-077.md) | E∞ Loader account-9 → account-10 skip chain | **done** |
| [svm-app-003](tasks/svm-app-003.md) | Non-Phoenix SDK reuse examples | **done** |

## 6. Track E — L3 sBPF bridge (`svm-sem-*`)

| Rung | ID | Slice | Status |
|---|---|---|---|
| E0 | (baseline) | Checked arith / store / branch ↔ Solanalib | **done** |
| E1 | [svm-sem-001](tasks/svm-sem-001.md) | Operand materialization + straightline | **done** |
| E2 | [svm-sem-002](tasks/svm-sem-002.md) | `.s` golden ↔ sbpfSemantics | **done** |
| E3 | [svm-sem-003](tasks/svm-sem-003.md) | Bounded CFG end-to-end (Counter) | **done** — 3-block increment; 7+5 / max+1 |
| E4 | [svm-sem-004](tasks/svm-sem-004.md) | AccountWords ↔ typed `storev` | **done** — Counter value word |
| E5 | [svm-sem-005](tasks/svm-sem-005.md) | Queue empty-push L3 | **done** |
| E∞ | [svm-sem-006](tasks/svm-sem-006.md)–[077](tasks/svm-sem-077.md) | walked `r7` + account-0..10 skip host knives | **doing** — account-10 skip landed; field arc open |
| E∞ | — | Loader-v3 + full host/ELF | **not a completion condition** |

## 7. Track F — engineering (`svm-eng-*`)

| ID | Slice | Status |
|---|---|---|
| [svm-eng-001](tasks/svm-eng-001.md) | Formalization gates in CI | **done** |
| [svm-eng-002](tasks/svm-eng-002.md) | This dual/triple matrix page | **done** |

## 8. Capability matrix cross-links

Descriptive runtime/SDK surface (not a promise list):

- [allocator-bounds.md](../modules/allocator-bounds.md) — account allocator does not lift bounded capacities
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
