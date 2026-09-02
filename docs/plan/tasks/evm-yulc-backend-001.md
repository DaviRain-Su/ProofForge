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
| Counter smoke | `scripts/smoke_yulc_counter.sh` — **verified** (2426 hex chars) |

## Verified (2026-09-01)

```bash
./scripts/build_yulc.sh          # yulc @ powdr-probe pin
./scripts/smoke_yulc_counter.sh  # ok
./runtime-tests/evm/anvil_yulc_counter.sh  # behavior match; bytecode differs
```

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

- CI optional lane: `runtime-tests/evm/yulc.sh` (see `evm-yulc-diff-001`)
- Expand dual-backend Anvil ladder beyond Counter
- `pf_store_*` lowering preprocessor for wider yulc coverage

## Acceptance

- [x] `pf build --target evm --backend=yulc` produces `.bin` when yulc accepts Yul
- [x] Counter smoke + Anvil behavior diff (see `evm-yulc-diff-001`)
- [ ] CI optional lane with cached yul-compiler build
