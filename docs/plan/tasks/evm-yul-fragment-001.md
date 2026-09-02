---
id: evm-yul-fragment-001
scope: evm
status: partial
depends-on: [evm-powdr-dep-001]
updated: 2026-09-01
---

# evm-yul-fragment-001 — ProofForge Yul ⊆ yul-compiler verified fragment

## Objective

Audit ProofForge `Emit.emitYul` output against the [powdr-labs/yul-compiler](https://github.com/powdr-labs/yul-compiler) verified fragment. Produce a machine-readable reject inventory and golden-program scan so Feature B (`--backend=yulc`) knows which contracts need lowering or must stay on solc.

## Deliverables

| Artifact | Purpose |
|---|---|
| `scripts/check_yul_fragment.py` | Regex/rule scan of `.yul` files or `--golden` emit |
| `scripts/emit_evm_golden_yul.lean` | Lean harness: Counter, Token, Ownable, … → stdout |
| This doc | Reject table + per-fixture expectations |

## Reject / caveat table (yul-compiler @ pin `c2e44cd2`)

| ID | Pattern / construct | Severity | yulc behavior | ProofForge today |
|---|---|---|---|---|
| **R1** | `gas()` builtin | **reject** | `compile = none` — gas oracle not realized | `EvmEnvironment` (`:= gas()`), all `call(gas(), …)` / `staticcall(gas(), …)` emit paths |
| **R2** | `linkersymbol("…")` (live) | **reject** | Needs `LinkEnv`; live delegatecall path reads `gas()` | Not emitted today |
| **R3** | Raw stack depth > 16 w/o layout | **reject** | `DUP16`/`SWAP16` ceiling; retries `stackLayoutBlock` + `memoryguard` spill | Mitigated by `memoryguard(4096)` prelude in every runtime object |
| **R4** | `pf_store_addr20` / `pf_store_fixed_bytes` | **warn** (PF-specific) | Not in `opTable` — must inline to `mstore`/`byte`/`shl` before yulc | Emitted in most wide-word / codec paths |
| **R5** | `memoryguard(n)` | **info** | Desugared scratch contract for spill fallback | Always in runtime prelude (`Emit.lean`) |
| **R6** | `setimmutable` / `loadimmutable` | **info** | Front-end desugar / PUSH32 placeholder; theorem gap on `setimmutable` meaning | Immutable-bearing fixtures (Ownable, Capped, Const) |
| **R7** | Nested `object` tree | **info** | Supported (`compileObject_correct`) | All `emitYul` output (deploy + runtime sub-object) |
| **R8** | `create` / `create2` | **warn** | Conditional on `ExternalsRealized` | Rare in golden set; audit per contract |
| **R9** | `selfdestruct` | **warn** | Conditional on `ExternalsRealized` | Not in default golden ladder |

## Golden expectations (`--golden --report-only`)

| Fixture | Expected errors | Expected warnings | Notes |
|---|---|---|---|
| Counter | 0 | `pf_store_*` possible | No external calls → no `gas()` |
| Token | `gas()` (precompile `staticcall`) | `pf_store_*` | EIP-712 `staticcall(gas(), 1, …)` |
| TipJar / Vault | `gas()` | `pf_store_*` | Native ETH `call(gas(), …)` |
| Ownable / Capped / Const | 0 | immutables + `pf_store_*` | No `gas()` reads in core paths |
| Wide | 0 | `pf_store_*` | Wide-word store helpers |

## Usage

```bash
# Inventory golden ladder (non-failing; errors are expected on Token/Vault)
python3 scripts/check_yul_fragment.py --golden --report-only

# CI-style self-test (synthetic + golden shape checks)
python3 scripts/check_yul_fragment.py --self-test

# Fail on yulc-hard rejects in a hand-written file
python3 scripts/check_yul_fragment.py path/to/program.yul
```

## Acceptance (remaining)

- [ ] Optional CI lane: `check_yul_fragment.py --self-test` (fast; no Mathlib).
- [ ] E-B2: lower `pf_store_*` helpers or add yulc preprocessor before dual-backend diff.
- [ ] E-B3: differential Anvil lane with allowlist for R1 fixtures.

## Related

- `evm-powdr-dep-001` — isolated `powdr-probe/` pins
- `multi-target-strategy.md` §2 E-B1 row
