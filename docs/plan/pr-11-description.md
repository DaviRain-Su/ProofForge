# PR #11 description (paste into GitHub if API cannot edit)

**Suggested title:** `productization: CLI/SDK split, init templates, and release (prod-001…004)`

Copy everything below the line into the PR body.

---

## Status

| | |
|---|---|
| **PR** | https://github.com/DaviRain-Su/ProofForge/pull/11 |
| **Branch** | `cursor/productization-split-4d63` → `main` |
| **Scope** | **Entire productization slice lives in this PR** (prod-001 → prod-004). |
| **Now** | prod-001…004 implemented + locally verified (full SVM/EVM Registry assemble + clean-dir git require). Waiting on GitHub CI. |
| **CI** | Ownership + Sdk import-closure + Sdk lib builds; full SVM/EVM digest lanes unchanged. |

Authority doc: [`docs/plan/productization.md`](../productization.md) (§7 is the live checklist).

---

## What shipped

### prod-001 — SDK import surface
- README recommends `ProofForge.Attr` + `ProofForge.Svm.Sdk` / `Evm.Sdk`
- `scripts/check_ownership.py` + shrink-only umbrella allowlist
- Sdk → Emit/Assemble/Registry banned

### prod-002 — Lake split + CLI discovery
- `lean_lib`s: `ProofForgeCore`, `ProofForgeSvmSdk`, `ProofForgeEvmSdk`, `ProofForge` (compiler + umbrella)
- CLI: `--module`, `pf.toml` `[[program]]`, bare names still → `Examples.*` + Registry digests
- `scripts/check_sdk_import_closure.py` in CI

### prod-003 — `pf init` + templates
- `pf init <name> --target svm|evm` copies `templates/*-counter` and rewrites require path
- Generated projects `lake build` with Sdk-only imports

### prod-004 — Release
- `.github/workflows/release.yml` on `v*` tags (linux/mac `pf` + checksums + notes)
- `pf --version` prints toolchain pins
- `docs/plan/release-capability-summary.md`

## Verify

```text
# Local full digest smoke (needs sbpf+solc):
#   ./scripts/smoke_productization.sh
#   lake exe pf -- build --target svm --out build/sbpf && lake exe pf -- build --target evm --out build/evm
python3 scripts/check_ownership.py
python3 scripts/check_sdk_import_closure.py
lake build ProofForgeSvmSdk ProofForgeEvmSdk pf
pf init demo --target svm && cd demo && lake build
lake exe pf -- build --target svm --module Examples.Counter   # from monorepo; needs sbpf for .so
```
