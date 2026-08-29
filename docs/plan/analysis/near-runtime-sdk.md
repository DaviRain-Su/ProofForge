# NEAR Runtime / SDK capability plan

> Updated 2026-08-29. This document maps the official `nearcore` host ABI and current
> `near-sdk-rs` architecture to ProofForge ownership boundaries. It is a dependency plan, not a
> claim of Rust SDK compatibility or mainnet readiness.

## 1. Rule: Runtime capability before SDK facade

```diagram
┌──────────────────────────────────────────────────────┐
│ Contract source                                      │
│ bounded business rules and explicit state changes    │
└──────────────────────────┬───────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────┐
│ Near.Sdk                                             │
│ AccountId, codec, storage layout, lifecycle policy,  │
│ Promise builder, callback decoding, event envelopes  │
└──────────────────────────┬───────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────┐
│ Near.Runtime / Ops / IR                              │
│ irreducible context, byte storage, logs, promise DAG │
└──────────────────────────┬───────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────┐
│ nearcore env ABI                                     │
│ registers, memory, storage, receipts, promise results│
└──────────────────────────────────────────────────────┘
```

The VM does **not** provide Vector, Map, Queue, JSON, Borsh, lifecycle annotations, typed events,
or synchronous contract calls. Those are compiler/SDK compositions over byte storage, register
I/O, logging, and promises. A new SDK name must not pretend a missing host or emitter path exists.

Authoritative source anchors:

- nearcore import table: [`runtime/near-vm-runner/src/imports.rs`](https://github.com/near/nearcore/blob/master/runtime/near-vm-runner/src/imports.rs)
- nearcore host semantics: [`runtime/near-vm-runner/src/logic/logic.rs`](https://github.com/near/nearcore/blob/master/runtime/near-vm-runner/src/logic/logic.rs)
- near-sdk environment facade: [`near-sdk/src/environment/env.rs`](https://github.com/near/near-sdk-rs/blob/master/near-sdk/src/environment/env.rs)
- Promise graph/builder: [`near-sdk/src/promise.rs`](https://github.com/near/near-sdk-rs/blob/master/near-sdk/src/promise.rs)
- current persistent collections: [`near-sdk/src/store/mod.rs`](https://github.com/near/near-sdk-rs/blob/master/near-sdk/src/store/mod.rs)
- generated entry lifecycle: [`near-sdk-macros/src/core_impl/code_generator/impl_item_method_info.rs`](https://github.com/near/near-sdk-rs/blob/master/near-sdk-macros/src/core_impl/code_generator/impl_item_method_info.rs)

## 2. Audited capability matrix

| Capability | Official owner | ProofForge now | Required owner here |
|---|---|---|---|
| register ABI | nearcore host | bounded reads for input/storage/context | Runtime memory/register contract |
| full AccountId | host bytes + SDK validation/type | **host context complete** in wsm-020; user decode absent | shared bounded bytes + Near SDK validation |
| u128 token/gas types | host LE-u128 + SDK wrappers | deposit/balance truncate to UInt64 | shared wide value + Near ABI binding |
| arbitrary KV/read/remove/exists | nearcore storage | ASCII keys, fixed 8-byte values, read/write only | Near Runtime storage effect |
| Borsh/JSON method ABI | generated SDK wrapper | raw zero/one UInt64 input, one UInt64 output | Near entry adapter/codec |
| contract `STATE` lifecycle | SDK Borsh convention | independent field keys | Near SDK policy; migration/version explicit |
| `store::Vector` | SDK over KV, prefix + `u32_le` index | fixed source vectors rejected by wasm dynamic ops | Near storage binding after bytes/Borsh |
| LookupMap/LookupSet | SDK over KV + key codec/hash policy | absent | Near storage binding; no host Map opcode |
| IterableMap/TreeMap | SDK composition | absent | after Vector + LookupMap; TreeMap last/optional |
| persistent Queue | no official exported Queue | absent | explicit bounded Vector/LookupMap + head/length policy |
| logs/events | `log_utf8`; NEP-297 SDK JSON | absent | Runtime log effect, then SDK event envelope |
| cross-contract call | promise receipt/action host ABI | absent | Runtime promise effects, then typed SDK builder |
| native transfer | Promise batch transfer action | absent | Runtime batch/action; never synchronous balance mutation |
| callback results | promise count/status/register + SDK decode | absent | bounded Runtime result read + SDK Result codec |
| private/payable/init | generated entry guards | absent | entry-adapter policy over context/storage |

Current NEAR therefore supports scalar state machines and context inspection, not yet a general
near-sdk-rs contract model.

## 3. Storage and collection contracts

### Three distinct shapes

1. Shared `Core.Value.BoundedVec` / `BoundedMap` / `BoundedQueue` define finite logical laws only.
2. Current NEAR v0 persists each flattened UInt64 state leaf under an ASCII field key.
3. Current `near-sdk-rs store::*` persists arbitrary serialized values under binary prefixes and
   collection-specific keys, often with explicit flush/cache behavior.

These cannot be called the same physical layout. In particular:

- `store::Vector` uses a `u32` length and `prefix || u32_le(index)` keys through its index map.
- `LookupMap` uses prefix + serialized/transformed key; identity/SHA-256/Keccak key policies differ.
- `IterableMap` composes a Vector of keys and a LookupMap of value/index records.
- current near-sdk-rs exports no persistent Queue. ProofForge must specify bounded capacity,
  head/tail arithmetic, stale-slot reachability, and storage reclamation itself.
- legacy `collections::Vector` uses a different `u64` index suffix and must never alias the current
  `store::Vector` compatibility name.

An early compile-time `field_0 … field_n` component may be useful, but it must be named
`FixedSlots` (or equivalent), not `store::Vector`, and must document that it is ProofForge-owned.

## 4. Promise and transfer contract

The minimum safe async chain is:

```diagram
┌─────────────────────┐
│ validated AccountId │
│ args/deposit/gas    │
└──────────┬──────────┘
           ▼
┌─────────────────────┐
│ promise create/batch│
│ function-call action│
└──────────┬──────────┘
           ▼
┌─────────────────────┐
│ promise_then        │
│ private self callback│
└──────────┬──────────┘
           ▼
┌─────────────────────┐
│ results_count/status│
│ bounded register read│
└──────────┬──────────┘
           ▼
┌─────────────────────┐
│ decode Result       │
│ value/promise_return│
└─────────────────────┘
```

Scheduling success is not remote execution success. `promise_result` status 1 is the only state in
which returned bytes may be read. Parallel joins cannot receive actions or be returned directly.
The SDK must reserve callback gas, authenticate self callbacks with full AccountId equality, and
make detach versus return explicit; it must not copy Rust `Drop`-realization implicitly.

Native transfer is `promise_batch_create(receiver)` plus `promise_batch_action_transfer(amount)`.
It depends on full AccountId and u128 and is asynchronous.

## 5. Dependency-ordered implementation

| Phase | Deliverable | Gate before advancing |
|---|---|---|
| N0 identity | lossless host AccountId + equality/self-call guard (**wsm-020 done**) | all eight zero-fill stores; high-word/length equality; sandbox 9-byte boundary |
| N1 byte/wide substrate | bounded bytes/string memory plan, UInt128 token values, bounded register reads, `value_return`/panic/log byte spans | resource budget; malformed length/OOB/UTF-8 failures |
| N2 entry ABI | canonical Borsh first, then JSON named objects; generated decode/call/encode wrapper | golden bytes against Rust; exact cursor/padding |
| N3 raw storage | arbitrary binary key/value, read/write/remove/exists, evicted value; explicit prefix ownership | view write/remove rejection; storage status matrix |
| N4 collections | current-layout Vector → LookupMap/Set → IterableMap/Set → bounded Queue; optional TreeMap last | independent consumers; layout golden tests; no hidden flush |
| N5 observability | bounded `log_utf8`, then exact NEP-297 `EVENT_JSON:` envelope | exact bytes and log-limit failures |
| N6 promises | create/then/and, batch function-call/transfer actions, explicit return | receipt DAG/gas/deposit/failure sandbox scenes |
| N7 callbacks | bounded result count/status/read, typed Result decode, private self callback | success/failure/oversized result and rollback scenes |
| N8 lifecycle | non-payable default, payable/private/init guards, `STATE` version/migration | repeated init, deposit rejection, migration fixtures |
| N9 standards | NEP-141/145 building blocks only after storage, events, transfer/call semantics | standard-specific integration suites |

## 6. Near-term task cuts

1. **NEAR-F0-BYTES:** bind existing bounded bytes/string and UInt128 values to a static,
   allocation-free NEAR memory/register plan. Do not add collections yet.
2. **NEAR-LOG:** add one bounded `log_utf8` Runtime effect and exact sandbox log observation.
3. **NEAR-STORAGE-RAW:** binary key/value read/write/remove/exists with explicit status results.
4. **NEAR-BORSH-ENTRY:** generated bounded Borsh input/output and stable state schema.
5. **NEAR-STORE-VECTOR:** current near-sdk-rs-compatible Vector key layout and explicit flush;
   then LookupMap/Set and a separately named bounded Queue.
6. **NEAR-PROMISE-1:** closed static receiver/method function call with explicit gas/deposit;
   callback/results follow in a separate slice.

Each task must pin host imports, memory ranges, bounds, view legality, canonical IR, assembly, and a
near-sandbox scene. Mainnet/testnet deployment remains a separate lifecycle gate.
