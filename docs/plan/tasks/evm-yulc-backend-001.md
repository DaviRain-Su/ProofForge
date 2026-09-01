---
id: evm-yulc-backend-001
scope: evm
status: partial
depends-on: [evm-yul-fragment-001]
updated: 2026-09-01
---

# evm-yulc-backend-001 — Optional yulc assembler backend

## Objective

Wire powdr-labs `yulc` as an alternate EVM bytecode backend alongside solc (Feature B),
without changing the default build path.

## Delivered (partial)

| Piece | Location |
|---|---|
| `Backend.solc \| .yulc` | `ProofForge/Evm/Assemble.lean` |
| `assembleProgramWithBackend` | same |
| CLI `--backend solc\|yulc` | `ProofForge/Cli.lean` |
| Env `PROOFFORGE_EVM_BACKEND` | `backendFromEnv` |
| Env `PROOFFORGE_YULC` | override yulc binary path |
| Build helper | `scripts/build_yulc.sh` |
| Counter smoke | `scripts/smoke_yulc_counter.sh` |

## Usage

```bash
./scripts/build_yulc.sh                    # one-time; Mathlib cold build ~10min
./scripts/smoke_yulc_counter.sh            # Counter via yulc + pf --backend yulc

lake exe pf -- build --target evm --backend yulc --out build/evm Counter
PROOFFORGE_EVM_BACKEND=yulc lake exe pf -- build --target evm Counter
```

## Fragment constraints

yulc rejects programs outside its verified fragment (see `evm-yul-fragment-001`).
Counter compiles; Token/Vault/TipJar fail on `gas()` until lowered or allowlisted.

## Still open (E-B3)

- CI optional lane: `smoke_yulc_counter.sh` after `build_yulc.sh`
- Anvil differential: solc vs yulc behavior (not bytecode bytes) for Counter/Capped
- `pf_store_*` lowering preprocessor for wider yulc coverage

## Acceptance

- [x] `pf build --target evm --backend=yulc` produces `.bin` when yulc accepts Yul
- [ ] Dual-backend Anvil regression with known-diff table
- [ ] Documented fragment allowlist in CI
