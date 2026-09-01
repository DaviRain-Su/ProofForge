# PR #11 description (paste into GitHub if API cannot edit)

**Suggested title:** `productization: CLI/SDK split, init templates, and release (prod-001…004)`

Copy everything below the line into the PR body.

---

## Status

| | |
|---|---|
| **PR** | https://github.com/DaviRain-Su/ProofForge/pull/11 |
| **Branch** | `cursor/productization-split-4d63` → `main` |
| **Scope** | **Entire productization slice lives in this PR** (prod-001 → prod-004). Do not open parallel productization PRs. |
| **Now** | Docs + template *skeletons* only. No Lake split / `pf init` / release workflow yet. |
| **CI** | Lean / SVM / EVM / NEAR should stay green on docs-only commits; later phases must keep digests stable. |

Authority doc: [`docs/plan/productization.md`](../productization.md) (§7 is the live checklist).

---

## Why

ProofForge already has CLI (`pf`) and target SDKs (`Svm.Sdk` / `Evm.Sdk`), but they are **coupled in one Lake package**:

1. `import ProofForge` pulls Emit / Assemble / Registry / all targets (~147 Examples still do this).
2. CLI hard-codes `Examples.<Name>` — external projects are not first-class.
3. No `pf init`, no installable SDK boundary, no versioned release of CLI + SDK.

Semantic ownership (apps must not import Emit) is mostly right; **distribution ownership** is missing.

---

## Target product shape

| Artifact | User gets | User does |
|---|---|---|
| **CLI `pf`** | Prebuilt binary (or `lake exe pf`) | `pf init` / `pf build` / `pf deploy` |
| **Target SDK** | Lean libs importable alone | Contract code: Attr + `Svm.Sdk` or `Evm.Sdk` only |
| **Templates** | Generated Lake project | Write `@[pf_entry]` against the SDK |

```
pf (compiler)                    Lake require (*Sdk @ tag)
     |                                  |
     | build                            v
     |                         ProofForgeSvmSdk / EvmSdk
     v                         (Runtime/Source for inline erase;
user module via --module/pf.toml    NO Emit/Assemble/Registry)
```

---

## Workstream in this PR (do in order)

### Done
- [x] Productization plan + INDEX / plan README links
- [x] Task cards prod-001 … prod-004
- [x] `templates/svm-counter` + `templates/evm-counter` skeletons (not isolation-buildable yet)

### P0 · prod-001 — freeze SDK import surface
- [ ] README / quickstart examples use SDK imports (not umbrella `ProofForge`)
- [ ] Extend `scripts/check_ownership.py` (or sibling):
  - [ ] **New** Examples files cannot `import ProofForge` (grandfather list, shrink-only)
  - [ ] `ProofForge/{Svm,Evm}/Sdk/**` cannot import same-target Emit / Assemble / Registry
- [ ] CI runs the gate; negative fixtures prove red
- [ ] Optional: migrate existing umbrella imports (does not block P0)

### P1 · prod-002 — Lake libs + CLI module discovery
- [ ] `lean_lib`s: `ProofForgeSvmSdk`, `ProofForgeEvmSdk`, `ProofForgeCompiler` (± Attr/Core)
- [ ] Umbrella `ProofForge.lean` = compiler workspace only; forbidden in user templates
- [ ] CI: SDK import-graph closure excludes Emit
- [ ] CLI: `--module` + root `pf.toml`; remove hard-coded `Examples.<Name>`
- [ ] In-repo Registry + Examples remain **compiler fixtures**, not product API
- [ ] Full SVM/EVM (+ existing WASM lane) green; **artifact digests unchanged**

### P2 · prod-003 — `pf init` + buildable templates
- [ ] `pf init <name> --target svm|evm`
- [ ] Copy from `templates/svm-counter` / `evm-counter`
- [ ] Emit `lakefile.lean`, `lean-toolchain`, `pf.toml`, minimal contract, README
- [ ] Templates `require` only the matching `*Sdk`
- [ ] Accept: temp dir `pf init` → `pf build` produces target artifacts
- [ ] near/xrpl templates later (after WASM SDK facade)

### P3 · prod-004 — release packaging
- [ ] Tag Release workflow: `pf` linux/mac + checksums + changelog
- [ ] Same tag `vX.Y.Z` for Lake `require … @ "vX.Y.Z"`
- [ ] `pf --version` prints CLI + toolchain pins
- [ ] Release notes: fail-closed capability summary
- [ ] Accept: clean machine install CLI + require SDK tag + template `pf build`

### Out of scope for this PR
- New contract syntax / new package manager
- Splitting to multiple git repos or an npm-style registry
- Changing on-chain semantics / IR digests / Runtime interpreters (unless P1 move is byte-identical)
- Replacing in-repo Examples with templates
- Unifying SVM vs EVM physical storage

---

## Merge policy

- Keep this PR open until **prod-001…004** are done (or explicitly descoped in the checklist).
- Land phases as successive commits on this branch; update `productization.md` §7 checkboxes each time.
- Prefer not to merge docs-only early if we are using this PR as the productization vehicle—unless you want an intermediate merge of P0 alone; say so and we will split.

## Test plan

- [x] Doc links resolve (plan / INDEX / prod tasks / templates README)
- [x] Templates document that isolation build waits on P1/P2
- [ ] After P0: ownership gate red on intentional violations; full CI green
- [ ] After P1: SDK-only elaborates a fixture contract; digests unchanged; CLI builds non-`Examples` module
- [ ] After P2: `pf init` + `pf build` for svm and evm in a temp directory
- [ ] After P3: release artifacts + clean-machine smoke
