# ProofForge

[English](README.md) · [简体中文](README.zh-CN.md)

[![Lean 4](https://img.shields.io/badge/Lean-4.31.0-blueviolet)](https://lean-lang.org)
[![Solana](https://img.shields.io/badge/target-Solana%20sBPF-14F195)](https://solana.com)
[![EVM](https://img.shields.io/badge/target-EVM%20Yul-627EEA)](https://ethereum.org)
[![CI](https://github.com/DaviRain-Su/ProofForge/actions/workflows/ci.yml/badge.svg)](https://github.com/DaviRain-Su/ProofForge/actions/workflows/ci.yml)
[![Website](https://img.shields.io/badge/website-GitHub%20Pages-0A0A0A)](https://davirain-su.github.io/ProofForge/)

**ProofForge** is a [Lean 4](https://lean-lang.org) compiler profile for **Solana** and **EVM** smart contracts. Write the contract as an ordinary `def`. Prove it as an ordinary `theorem`. Compile the same subject to on-chain bytes.

It is **not** a new contract language. There is no `program … where`. Mark callable roots with `@[pf_entry]`. The CLI is `pf`.

Current targets: **Solana sBPF** (`.so` / IDL) and **EVM Yul** (`.bin` / ABI).

- Website: [https://davirain-su.github.io/ProofForge/](https://davirain-su.github.io/ProofForge/)
- Docs index: [docs/INDEX.md](docs/INDEX.md)

## Why this exists

Lean 4 is already an executable language and a proof assistant. ProofForge only adds the on-chain profile:

| Principle | What it means |
| --- | --- |
| **One subject** | Theorems pin the user `def`. Compile walks the same extracted IR. You never prove A and emit B. |
| **Fail-closed subset** | Profile admits only what can lower on-chain. `IO`, `partial`, `sorry`, `@[extern]`, `@[implemented_by]`, and unbounded recursion are refusals, not warnings. |
| **Two profiles, one Core** | SVM and EVM share Lean / Profile / Extract / CFG. They do **not** share a physical store. |
| **Honest trust boundary** | The kernel accepts theorems about the `def` / IR. That is not a claim about the loader or mainnet. |

## Pipeline

```
ordinary Lean def / theorem     ← Lean owns this
        │
        ▼
Profile (fail-closed subset)
        │
        ▼
Extract Expr → typed Core + target-neutral Ops
        │
   ┌───┴───┐
   ▼         ▼
SVM IR     EVM IR
+ IDL      + ABI
   │         │
   ▼         ▼
sBPF / .so   Yul / .bin
```

`#pf_build Examples.Counter` extracts inside Lean. `pf build --target svm` walks the same IR.

## Quick start

### 1. Pin the toolchain

Do not substitute a random assembler from `PATH`. Install the locked versions with:

```bash
./.agents/setup
```

| Tool | Version | Role |
| --- | --- | --- |
| Lean 4 | `v4.31.0` | Source language and kernel |
| sbpf | `0.2.2` | Assemble `.s` → Solana `.so` |
| solc | `0.8.34` | Assemble Yul → EVM `.bin` |
| Surfpool | `1.5.0` | Loader-v3 local deploy (not `solana-test-validator`) |
| Foundry / Anvil | `1.7.1` | EVM engineering gate |
| Rust | `1.90.0` | Mollusk runtime tests |

### 2. Build the compiler

```bash
lake build
```

This type-checks ProofForge, the examples, and produces the `pf` executable. It does **not** emit on-chain artifacts.

### 3. Compile a contract

`pf` re-extracts IR from the user module. It does not assemble a legacy Golden fixture.

```bash
# Solana: Counter.so / Counter.s / Counter.idl.json
lake exe pf -- build --target svm --out build/sbpf Counter

# EVM: Counter.bin / Counter.yul / Counter.abi.json
lake exe pf -- build --target evm --out build/evm Counter
```

`--target svm` also accepts `solana` or `sbpf`. Omit the program name to build every registered module for that target. See `lake exe pf -- --help`.

| Target | Artifacts | Layout |
| --- | --- | --- |
| SVM | `.so` / `.s` / `.idl.json` | Solana IDL spec 0.1.0, Loader V3 |
| EVM | `.bin` / `.yul` / `.abi.json` | Selector / storage slots / ABI |

## Write a contract

Start with [`Examples/Counter.lean`](Examples/Counter.lean): one account, `UInt64`, checked add. Entries are ordinary Lean.

```lean
import ProofForge

namespace Examples.Counter

structure State where
  value : UInt64

inductive Error where
  | overflow

@[pf_entry]
def init (initial : UInt64) : State :=
  { value := initial }

@[pf_entry]
def increment (s : State) (delta : UInt64) :
    Except Error (State × UInt64) :=
  if s.value ≤ u64Max - delta then
    let next := s.value + delta
    .ok ({ value := next }, next)
  else
    .error .overflow
```

Inline helpers with `@[pf_inline]`. Lean still owns business typing. Extract authority is the elaborated `Expr` closure, not `Lean.Compiler.IR`.

## Prove a contract

Theorems live in the same file, in a `Proofs` section. They are ordinary kernel-checked properties of the `@[pf_entry]` functions.

First batch (Counter, Capped, Token):

- success-path postconditions
- monotonicity
- Token supply effect
- Capped cap invariant

They depend only on the standard axioms `propext` / `Quot.sound`. CI (`scripts/check_no_sorry.py`) refuses placeholders in the proof batch. Proof subject and compile subject must share the same IR digest.

## Runtime tests

These are **not** part of `lake build`. Run them after `pf` has written artifacts.

### Mollusk (Solana unit)

Environment variables use the `PF_*_SO` prefix:

```bash
(cd runtime-tests/solana && \
  PF_COUNTER_SO=../../build/sbpf/Counter.so \
  cargo test --locked --test counter)
```

### Surfpool (Loader-v3 deploy)

Phoenix and the Phoenix-v1 profile verifier deploy through Surfpool, not `solana-test-validator`:

```bash
runtime-tests/surfpool/smoke.sh
runtime-tests/surfpool/smoke.sh PhoenixV1Profile
```

EVM engineering gate is pinned Anvil. v0 refuses public broadcast.

## Targets

### Solana (sBPF / Loader V3)

SVM owns account geometry, CPI, and IDL. Persistent maps and queues are fixed-capacity POD views on account bytes. Heap is an invocation-local downward bump (32 KiB, up to 256 KiB): dealloc does not reclaim, and pointers never enter accounts.

Compiler boundary:

- `Svm.EntryAdapter` owns packed wire decode, raw/generated dispatch, and the account prefix.
- `Svm.AccountStorage` owns in-account Region/Field and bounded `Query` / `Call` (map, queue, allocator, tree).
- Generic Ops / IR / CFG / main Emit dispatch `component` once. New containers extend a component-owned module; they do not cut sideways through Extract or the main emitter.

### Phoenix-v1 (largest SVM slice)

[`Examples/PhoenixV1Profile.lean`](Examples/PhoenixV1Profile.lean) is the current stress test of that boundary — not a special-case compiler.

| Area | What is in tree |
| --- | --- |
| Storage | 128-seat trader tree and two 512-node order books live in account bytes. Slots are one-based (`0` is sentinel). No heap `Map`, detached node, copied tree, or out-of-account pointer. |
| Matching | Fixed-capacity Sokoban insert/remove, trader get-or-register deposit, bid/ask `ReduceOrderWithFreeFunds` (partial and full), collateral unlock, checked preflight. |
| Official tags 4–7 | Tag 6/7 `FifoCancel` cancels in place (bids→asks, per-side FIFO) with owner filter, unlock, event index, and released-lot accumulator. Tag 6 then claim/withdraw quote→base. Tag 7 never enters Token CPI. |
| Audit | `BatchRecorder.begin/append/finish` uses the official SDK `0x300000000` / 32 KiB downward bump. 32 × 35-byte Reduce records flush before the 33rd. Empty finish still emits a 93-byte header-only batch. Heap addresses do not enter source or accounts. |
| Cursors | PDA mint seeds read an authenticated `MarketHeader` byte slice. FIFO cursors keep a `(price, sequence)` scalar key and walk a bounded strict upper-bound from the account root. Deletes do not store node addresses or collect a heap `Vec`. |

Next on the same component boundary: official tags 8/9 `CancelUpTo`. Details: [docs/modules/phoenix.md](docs/modules/phoenix.md).

### EVM (Yul / ABI)

EVM shares ordinary Lean, Profile, Extract, and Core CFG with SVM. It does **not** copy SVM account geometry.

Contract source opens `ProofForge.Evm.Sdk`:

- `Storage.Layout` is a compile-time cursor for typed hashed maps
- `Address`, `UInt256`, `Context`, `Immutable`, `Event`, `Revert`
- closed-call facade — it does not hide `.ok` / `.error`

Descriptors erase at extract time and never enter storage. `Examples.Token` and `Examples.Capped` already sit on this surface with an unchanged target IR digest.

## Trust boundary

| Claim | Meaning |
| --- | --- |
| **Weak (public v0)** | The kernel accepted theorems about the user `def` / extracted IR. TCB = Lean kernel + subject binding. |
| **Engineering** | The same IR, through the emitter and pinned `sbpf` / `solc`, matches fixtures on Mollusk or Anvil. |
| **Not claimed** | `.so` / loader / full SVM refinement / theorem ⇒ deployed program. A theorem does not imply a correct public deployment. |

On-chain discriminators and layout still use the `proof-forge-solana-v1:` domain. Renaming this repository does not change chain bytes.

## Website

The product site lives in [`website/`](website/) — same repository, not a second project. GitHub Pages: [https://davirain-su.github.io/ProofForge/](https://davirain-su.github.io/ProofForge/).

```bash
cd website && npm install && npm run dev
```

After the first merge, set **Settings → Pages → Source** to GitHub Actions.

Remote MCP serves docs and scaffold guidance only. It does not spawn Lean, hold keys, or broadcast:

```text
https://proof-forge-mcp.davirain-yin.workers.dev/mcp
```

## Related project

[proof_forge](https://github.com/DaviRain-Su/proof_forge) is the earlier `program … where` DSL. This repository reuses Lean syntax itself and extracts the fail-closed subset that can lower on-chain.

## Documentation

Start at [docs/INDEX.md](docs/INDEX.md).

| Doc | Role |
| --- | --- |
| [01-prd.md](docs/01-prd.md) | In / out of scope |
| [02-architecture.md](docs/02-architecture.md) | Module and trust boundaries |
| [modules/README.md](docs/modules/README.md) | Per-module contracts |
| [plan/svm-work-plan.md](docs/plan/svm-work-plan.md) | Current SVM mainline |
