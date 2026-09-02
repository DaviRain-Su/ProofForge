# release-001 — Cut first public tag `v0.0.1`

**Status:** checklist only — do **not** push the tag or create a GitHub Release from this card alone.  
**Depends on:** [prod-004](prod-004.md) (workflow + pins landed).  
**Proposed tag:** `v0.0.1` (matches `lakefile.lean` `version := v!"0.0.1"` and `pf --version`).

## Readiness (as of this card)

| Item | Ready? | Notes |
|---|---|---|
| `.github/workflows/release.yml` | yes | Triggers on `push` tags `v*`; does not affect PR CI |
| `docs/plan/release-capability-summary.md` | yes | Inlined into Release notes by the workflow |
| `pf --version` pins | yes | CLI / Lean / sbpf / solc / wat2wasm / foundry |
| Lake SDK libs | yes | `ProofForgeSvmSdk` / `ProofForgeEvmSdk` (+ `ProofForgeCore`) |
| Templates + `pf init` | yes | `templates/svm-counter`, `templates/evm-counter` |
| Existing `v*` tags / GitHub Releases | none | First cut is greenfield |

**Verdict:** release.yml + productization P3 are sufficient to cut the first tag. Remaining work is procedural (merge → tag → smoke), not missing workflow plumbing. Soft gaps below do not block the workflow from publishing.

## What `release.yml` produces

On `git push origin v0.0.1` (annotated or lightweight):

1. **build-linux** (`ubuntu-24.04`): `lake build pf` → uploads artifact `pf-linux`
2. **build-macos** (`macos-14`): `lake build pf` → uploads artifact `pf-macos`
3. **publish** (`softprops/action-gh-release`): GitHub Release for that tag with:

| Asset | Purpose |
|---|---|
| `pf-linux-x86_64` | Linux CLI binary |
| `pf-linux-x86_64.sha256` | checksum |
| `pf-macos-aarch64` | macOS aarch64 CLI binary |
| `pf-macos-aarch64.sha256` | checksum |
| `pf-version.txt` | `pf --version` capture from the builder |

Release body (generated, not a checked-in file):

- CLI asset list
- Lake `require «proofforge» … @ "v0.0.1"` snippet
- Contents of `docs/plan/release-capability-summary.md`
- Quick-start hint (`pf init` → pin require → build)

SDK distribution is the **same git tag** (source via Lake `require`), not a separate tarball.

## Pre-flight (before anyone pushes the tag)

```bash
# 1. Land productization + CI on main (PR #14 absorbs CI gates; productization already on main lineage)
git checkout main && git pull origin main
# Confirm CI green on the commit you will tag.

# 2. Version agreement (must all say 0.0.1)
rg -n '0\.0\.1' lakefile.lean ProofForge/Cli.lean templates/*/lakefile.lean
cat lean-toolchain   # leanprover/lean4:v4.31.0

# 3. No prior tag
git fetch --tags
git tag -l 'v0.0.1'
gh release list

# 4. Local gates (optional but recommended)
./scripts/ci_local.sh --fast
```

## Exact commands to cut `v0.0.1` (human operator)

```bash
# On the commit that should be public (prefer main after merge — not a draft PR tip)
git checkout main
git pull origin main
git log -1 --oneline

git tag -a v0.0.1 -m "ProofForge v0.0.1 — first CLI + SDK tag"
git push origin v0.0.1

# Watch the Release workflow (do not create the Release manually)
gh run watch --repo DaviRain-Su/ProofForge
gh release view v0.0.1 --repo DaviRain-Su/ProofForge
```

Do **not** use `gh release create` — `release.yml` owns the Release.

## SDK require snippet (user projects)

```lean
require «proofforge» from git
  "https://github.com/DaviRain-Su/ProofForge.git" @ "v0.0.1"
```

Contract imports stay Sdk-only:

```lean
import ProofForge.Attr
import ProofForge.Svm.Sdk   -- or ProofForge.Evm.Sdk
```

Do **not** `import ProofForge` (umbrella) in user contracts. Lake libs on the tag: `ProofForgeSvmSdk` / `ProofForgeEvmSdk` (+ `ProofForgeCore`).

## Smoke acceptance (clean machine)

Goal: install Release CLI → require the tag → init template → produce artifacts.

### A. Install CLI from the Release

```bash
# Linux example
mkdir -p "$HOME/.local/bin"
curl -fsSL -o "$HOME/.local/bin/pf" \
  "https://github.com/DaviRain-Su/ProofForge/releases/download/v0.0.1/pf-linux-x86_64"
chmod +x "$HOME/.local/bin/pf"
pf --version
# expect: pf 0.0.1 (ProofForge) + lean / sbpf / solc / wat2wasm pin lines
```

### B. Toolchain pins on the clean machine

Match `pf --version` / `.agents/setup`:

- elan + `lean-toolchain` (`leanprover/lean4:v4.31.0`)
- SVM assemble: `sbpf 0.2.2` @ `d835bc6…`
- EVM assemble: `solc 0.8.34+commit.80d5c536`

(Easiest mirror of CI pins: clone the tag and run `./.agents/setup` on Linux.)

### C. Init + pin require + build

`pf init` reads `templates/*` from the **current working directory** (ProofForge checkout). On a machine with only the binary, shallow-clone the tag for templates, then rewrite the generated `lakefile.lean` to the git require.

```bash
git clone --depth 1 --branch v0.0.1 \
  https://github.com/DaviRain-Su/ProofForge.git /tmp/ProofForge-v0.0.1
cd /tmp/ProofForge-v0.0.1

pf init /tmp/pf-smoke-svm --target svm

# Replace path require with the published tag (templates comment already shows this shape)
cat > /tmp/pf-smoke-svm/lakefile.lean <<'EOF'
import Lake
open Lake DSL

package «my-program» where
  version := v!"0.1.0"

require «proofforge» from git
  "https://github.com/DaviRain-Su/ProofForge.git" @ "v0.0.1"

@[default_target]
lean_lib «MyProgram»
EOF

cd /tmp/pf-smoke-svm
lake build

# Prefer Lake's package env so OLEANs resolve (standalone `pf` alone is not enough):
lake env pf build --target svm
# Equivalent without the Release binary:
#   lake exe pf -- build --target svm

ls out/*.so out/*.idl.json   # SVM success
```

Optional EVM twin: `pf init /tmp/pf-smoke-evm --target evm`, same require pin, then `lake env pf build --target evm` and check `out/*.bin`.

### Pass criteria

1. Release assets listed above exist; sha256 matches.
2. `pf --version` reports `0.0.1` and the documented pins.
3. Clean-dir template with `@ "v0.0.1"` completes `lake build` + `pf build` and writes SVM `.so` (and/or EVM `.bin`).
4. User lakefile does not path-require a monorepo checkout.

## Soft gaps (do not block first tag)

1. **`pf init` needs a checkout** for `templates/` (cwd-relative). Binary-only machines must shallow-clone the tag (or copy `templates/`) once.
2. **Standalone `pf` needs `lake env`** (or `lake exe pf`) so Lean finds package OLEANs; bare `pf build` outside Lake env will fail import.
3. **Cut from `main` after CI is green** — tagging a draft PR tip works mechanically but is a product footgun.
4. **`fail_on_unmatched_files: false`** on the publish step — prefer fixing missing assets over silent omission; both OS jobs must still succeed for `publish` to run.
5. **No NEAR/XRPL templates** yet (explicitly deferred in productization).
6. Bumping the public number to `v0.1.0` later is fine, but requires a coordinated bump of `lakefile.lean`, `ProofForge/Cli.lean`, and template comments — do not cut `v0.1.0` while those still say `0.0.1`.

## After smoke passes

- [ ] Tick “首次 tag 后干净机器验收” on [prod-004](prod-004.md)
- [ ] Point README / Quickstart at the Release URL
- [ ] Only then consider Phoenix out-of-tree (needs a stable SDK tag)
