# NEAR Runtime / SDK capability plan

> Updated 2026-08-30. This document maps the official `nearcore` host ABI and current
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
| guest linear-memory allocation | near-sdk-rs guest allocator over Wasm `memory.grow`; no nearcore malloc host import | **checked invocation-local arena + `Buffer64` complete** in wsm-near-memory-001 | Near Memory/Emit substrate; SDK exposes bounded consumers, never raw pointers |
| register ABI | nearcore host | bounded reads for input/context/raw storage/callback results; exact status and stale-register rules | Runtime memory/register contract |
| full AccountId | host bytes + SDK validation/type | **host context complete** in wsm-020; user decode absent | shared bounded bytes + Near SDK validation |
| u128 token/gas types | host LE-u128 + SDK wrappers | **deposit/balance, checked add/sub, and exact Borsh storage values complete** in wsm-near-u128-001/u128-arithmetic-001/u128-storage-001; explicit gas and lossless Promise deposit complete | shared wide value + Near ABI binding |
| arbitrary KV/read/remove/exists | nearcore storage | **bounded exact-key read/write/remove/has-key complete** in wsm-near-storage-001, alongside fixed scalar slots | Near Runtime storage effect |
| Borsh/JSON method ABI | generated SDK wrapper | canonical bounded bytes/String input in wsm-near-bytes-001 and allocator-backed bounded bytes/String/unsigned-array view output in wsm-near-output-001; nested/tagged/JSON absent | Near entry adapter/codec |
| contract `STATE` lifecycle | SDK Borsh convention | **one-time init, fail-closed entries, versioned schema envelope, and authenticated split-key migration complete** in wsm-near-init/uninitialized/state-envelope/migration-001 | broader state codecs/version chains explicit |
| `store::Vector` | SDK over KV, prefix + `u32_le` index | **bounded direct UInt64 element layout foundation complete** in wsm-near-vector-001; full metadata/cache/generic API absent | Near storage binding after bytes/Borsh |
| LookupMap/LookupSet | SDK over KV + key codec/hash policy | **direct default-Identity UInt64 layout foundation complete** in wsm-near-lookup-001; cache/custom hash/generic API absent | Near storage binding; no host Map opcode |
| IterableMap/TreeMap | SDK composition | **bounded Identity IterableMap/IterableSet complete** in wsm-near-iterable-001; TreeMap absent | after Vector + LookupMap; TreeMap last/optional |
| persistent Queue | no official exported Queue | **ProofForge bounded Queue64 complete** in wsm-near-queue-001 | explicit bounded Vector/LookupMap + head/length policy |
| logs/events | `log_utf8`; NEP-297 SDK JSON | static/bounded logs, bounded string-data envelope, and exact NEP-141 mint/transfer/burn with bounded optional memos complete | standard-specific integration next; generic JSON absent |
| cross-contract call | promise receipt/action host ABI | **detached/returned static calls, native transfers, authenticated self-callback, and closed ordered two-child join complete** in wsm-near-promise-001/002/then/private/transfer/and-001 | Runtime promise effects, then typed SDK builder |
| native transfer | Promise batch transfer action | **static detached/returned lossless-u128 transfer complete** in wsm-near-promise-transfer-001 | Runtime batch/action; never synchronous balance mutation |
| callback results | promise count/status/register + SDK decode | **bounded count/status/register read, strict Borsh UInt64 decode, and genuine chained success/failure/oversized scenes complete** in wsm-near-promise-result/then/codec-001 | bounded Runtime result read + SDK Result codec |
| private/payable/init | generated entry guards | **explicit private/payable/migration metadata, generated wrapper ordering, donation-only payable, repeated-init/uninitialized/schema/migration guards complete** | entry-adapter policy over context/storage |

Current NEAR therefore supports scalar state machines, context inspection, top-level bounded Borsh
bytes/String input, bounded bytes/String/unsigned-array view output, bounded raw binary storage,
fixed-width Vector/Identity LookupMap/LookupSet/IterableMap/IterableSet and ProofForge Queue
foundations, explicit detached and returned static cross-contract function calls, one returned
static self-callback edge authenticated by full AccountId equality, and bounded callback-result
observation with strict UInt64 decode, explicit detached and returned static native transfers, and
one closed ordered two-child join feeding a self callback.
It is not yet a general near-sdk-rs contract model.

## 3. Storage and collection contracts

### Three distinct shapes

1. Shared `Core.Value.BoundedVec` / `BoundedMap` / `BoundedQueue` define finite logical laws only.
2. Current NEAR v0 persists each flattened UInt64 state leaf under an ASCII field key.
3. Current `near-sdk-rs store::*` persists arbitrary serialized values under binary prefixes and
   collection-specific keys, often with explicit flush/cache behavior.

These cannot be called the same physical layout. In particular:

- `store::Vector` uses a `u32` length and `prefix || u32_le(index)` keys through its index map.
- `LookupMap` uses prefix + serialized/transformed key; identity/SHA-256/Keccak key policies differ.
- wsm-near-lookup-001 implements only Identity `Prefix4 || Borsh(UInt64)`: map values are Borsh UInt64 and
  set values are empty bytes. Map writes are immediate rather than cache/flush/Drop compatible.
- `IterableMap` composes a Vector of keys and a LookupMap of value/index records.
- current near-sdk-rs exports no persistent Queue. ProofForge must specify bounded capacity,
  head/tail arithmetic, stale-slot reachability, and storage reclamation itself.
- legacy `collections::Vector` uses a different `u64` index suffix and must never alias the current
  `store::Vector` compatibility name.

An early compile-time `field_0 … field_n` component may be useful, but it must be named
`FixedSlots` (or equivalent), not `store::Vector`, and must document that it is ProofForge-owned.
The wsm-near-memory-001 arena supplies only invocation-local serialized key/value buffers, codec
scratch, and explicit caches. Every durable collection element, length, index, and lifecycle marker
remains in NEAR KV storage; arena addresses must never become collection layout or persistent state.

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
The explicit returned path calls `promise_return` only after caller state persistence; this links
the child outcome without waiting and prevents a later scalar `value_return` from replacing the
forwarded result. Bounded callback-result inspection preserves exact status and only reads a
successful register. The first static self-callback edge now uses `promise_batch_then`, keeps
callback input independent, and returns the callback receipt. Strict UInt64 decoding and a full
predecessor/current AccountId guard now run before dependency-result access; broader codecs and
general Promise handles remain absent. The closed join edge stages two concrete Promise indices in
left/right order, immediately calls `promise_and(ptr, 2)`, uses the joint Promise only as a
`promise_batch_then` dependency, and returns only the callback receipt. Failed children still
release the callback and retain their ordered status-2 result slots.

Native transfer now uses `promise_batch_create(receiver)` plus
`promise_batch_action_transfer(index, amountPtr)`. Its exact 16-byte LE u128 amount frame is staged
through the guest arena. The SDK exposes explicit detached and returned variants, and the latter
links the transfer receipt only after caller state persistence. Static variants retain their
compile-time validated receiver bytes. wsm-near-promise-account-transfer-001 adds closed dynamic
variants for a complete nominal `AccountId`: exactly `length` active raw bytes (2..64) are staged,
with no Borsh length, JSON transform, truncation, or inactive carrier padding. Both forms remain
asynchronous; dynamic handles and multi-action builders are absent.

## 5. Dependency-ordered implementation

| Phase | Deliverable | Gate before advancing |
|---|---|---|
| N0 identity | lossless host AccountId + equality/self-call guard (**wsm-020 done**) | all eight zero-fill stores; high-word/length equality; sandbox 9-byte boundary |
| N1 byte/wide substrate | **UInt128 token context, checked two-limb add/sub, and exact u128×u64 done** in wsm-near-u128-001/u128-arithmetic-001/u128-mul-001, static UTF-8 data spans in wsm-near-log-001, and bounded bytes/string input frames/register reads done in wsm-near-bytes-001 | resource budget; malformed length/OOB/UTF-8 failures |
| N2 guest arena | **checked invocation-local allocation, growth, reset, zeroing, and pointer-free `Buffer64` done** in wsm-near-memory-001 | model/emitter/WAT/sandbox bounds and trap matrix |
| N3 entry ABI | canonical bounded Borsh input done in wsm-near-bytes-001; allocator-backed bounded bytes/String/unsigned-array view output done in wsm-near-output-001; nested/tagged values, mutating output, and JSON remain | golden bytes against Rust; exact cursor/padding |
| N4 raw storage | **done in wsm-near-storage-001:** arbitrary binary key/value, read/write/remove/exists, evicted value; allocator-backed bounded register copies and explicit prefix ownership | view write/remove rejection; storage status matrix |
| N5 collections | **DirectVector64 done in wsm-near-vector-001, direct Identity LookupMap64/LookupSet64 done in wsm-near-lookup-001, ProofForge bounded Queue64 done in wsm-near-queue-001, and bounded Identity IterableMap64/IterableSet64 done in wsm-near-iterable-001**; full collection metadata follows N9 lifecycle; optional TreeMap last | independent consumers; layout golden tests; durable KV only; no hidden flush |
| N6 observability | static and bounded dynamic `log_utf8` plus exact bounded NEP-297 string-data envelope done in wsm-near-log-001/log-dynamic-001/event-001 | exact standard-specific event bytes and host log limits |
| N7 promises | **detached/returned static batch calls, static/full-AccountId native transfers, self-callback, and ordered two-child join done in wsm-near-promise-001/002/then/transfer/account-transfer/and-001**; arbitrary-N/nested joins and handles remain | receipt DAG/gas/deposit/failure sandbox scenes |
| N8 callbacks | **bounded result count/status/read, strict UInt64 decode, full-AccountId private guard, and genuine chained result scenes done in wsm-near-promise-result/then/codec/private-001**; broader codecs remain | success/failure/oversized/result-auth rollback scenes |
| N9 lifecycle | **repeated-init, private/payable wrappers, fail-closed entries, versioned schema envelope, and authenticated migration done** in wsm-near-init/payable/entry-policy/uninitialized/state-envelope/migration-001 | private/deposit/state ordering, real V1→V2 migration fixture |
| N10 standards | exact NEP-141 mint/transfer/burn events with no-memo and bounded-memo APIs complete; closed checked balance/total-supply ledger policy complete; no public token method contract | standard-specific integration suites |
| N11 storage economics | real invocation-dynamic `storage_usage`, closed caller-only measured registration, and exact-zero unregister complete; storage byte price remains explicit trusted protocol config | variable AccountId-key cost/reclaim, speculative mutation rollback, exact refunds; no force or public NEP-145 ABI |

## 6. Near-term task cuts

1. **NEAR-F0-BYTES (wsm-near-bytes-001 done):** bounded bytes/string use a static, allocation-free NEAR
   memory/register input plan with exact canonical Borsh input and strict String UTF-8.
2. **NEAR-MEMORY (wsm-near-memory-001 done):** checked guest arena over Wasm linear memory, exposed only
   through bounded pointer-free consumers; future codec/storage/promise scratch builds on it.
3. **NEAR-LOG:** static literals, arena-backed bounded dynamic UTF-8 spans, and one exact bounded
   NEP-297 string-data envelope are complete in wsm-near-log-001/log-dynamic-001/event-001;
   standard-specific closed payloads follow, while generic JSON remains absent.
4. **NEAR-NEP-141-EVENT:** exact v1.0.0 `ft_mint`, `ft_transfer`, and `ft_burn` serialization,
   including bounded optional memo variants, is complete in wsm-near-nep141-event-001/002/003.
   A closed balance/supply policy is complete separately; public FT methods and storage management
   remain later slices.
   The ledger dependency chain now has checked NearToken add/sub, exact Borsh-u128 values, and a
   specialized raw-Identity Prefix4 AccountId-to-NearToken map in
   wsm-near-u128-arithmetic-001/u128-storage-001/account-token-map-001. The internal raw-key budget is independently
   widened to the exact 72-byte `Prefix4 || Borsh(AccountId)` maximum in
   wsm-near-storage-key-001. wsm-near-fungible-ledger-001 composes those prerequisites with
   prechecked mint/burn/transfer and lossless total supply, but remains separate from public ABI,
   registration/storage management, resolver, deposits, and events.
   wsm-near-storage-economics-001 adds the real nearcore `storage_usage` context leaf and measured
   storage deltas. It intentionally does not guess `storage_amount_per_byte`: current near-sdk-rs
   and nearcore expose no guest `storage_byte_cost`, so registration charging still needs an
   explicit trusted network/config boundary.
   wsm-near-u128-mul-001 supplies the checked full-width `NearToken × UInt64` operation needed to
   turn measured bytes into a configured cost. wsm-near-promise-account-transfer-001 now supplies
   detached/returned native transfer to a complete dynamic AccountId; closed registration policy
   composes this refund edge in wsm-near-storage-registration-001 without pretending the public
   NEP-145 ABI already exists. It registers only `Context.caller` as a present-zero balance,
   measures that caller's actual variable key delta, and relies on nearcore receipt rollback after
   the speculative write for insufficient-deposit or arithmetic failures.
   wsm-near-storage-unregister-001 separately requires exactly one attached yocto, removes only an
   exact present-zero caller key, measures the live reclaim, and refunds `reclaim × trustedPrice + 1`.
   Missing returns false and retains the yocto as current near-sdk-rs does; current near-sdk-rs
   otherwise refunds a configured fixed maximum, whereas this closed policy deliberately prices
   the live variable key. A synchronous post-remove panic rolls storage back, but later detached
   refund receipt failure does not restore the committed key.
5. **NEAR-BORSH-OUTPUT (wsm-near-output-001 done):** allocator-backed bounded bytes/String/unsigned-array view
   output has an independent plan and canonical active prefix; nested/tagged/JSON remain later.
6. **NEAR-STORAGE-RAW (wsm-near-storage-001 done):** binary key/value read/write/remove/exists with exact
   nearcore status/stale-register behavior and allocator-backed bounded register reads.
   **NEAR-STORAGE-KEY (wsm-near-storage-key-001 done):** only internal key frames accept 1..72;
   values/results/public Borsh frames retain 1..64, and an exact 72-byte raw key is sandbox-pinned.
7. **NEAR-STORE-VECTOR (wsm-near-vector-001 done):** bounded direct-write UInt64 elements use exact current
   near-sdk-rs bare-prefix keys and Borsh values. Immediate persistence is explicit; full Rust
   metadata/cache/Drop semantics wait for the `STATE` lifecycle instead of being simulated.
8. **NEAR-STORE-LOOKUP (wsm-near-lookup-001 done):** default Identity UInt64 map/set keys and values match
   current near-sdk-rs durable bytes; direct map timing/raw statuses remain explicitly narrower.
9. **NEAR-STORE-QUEUE (wsm-near-queue-001 done):** ProofForge-owned bounded FIFO slots reuse the Vector
   key/value recipe; caller state owns canonical head/length, wraparound, and drained reset while
   pop immediately reclaims the front key. Current near-sdk-rs exports no Queue.
10. **NEAR-STORE-ITERABLE (wsm-near-iterable-001 done):** bounded Identity UInt64 map/set layouts derive exact
   `P || 'v'` and `P || 'm'` namespaces, preserve replacement order, and repair moved index records
   during fail-closed swap-remove. Immediate persistence does not claim Rust cache/`Drop` timing.
11. **NEAR-PROMISE-1 (wsm-near-promise-001 done):** closed static receiver/method detached function call with
    bounded arguments, explicit gas, and lossless u128 deposit. It emits batch create/action without
    `promise_return`; chaining, callbacks, and results remain separate slices.
12. **NEAR-PROMISE-2 (wsm-near-promise-002 done):** explicit static returned call shares Promise staging,
    persists caller state, and then links the concrete receipt with final `promise_return`. Remote
    success bytes and failure propagate; callback inspection and `promise_then` remain later.
13. **NEAR-PROMISE-RESULT-1 (wsm-near-promise-result-001 done):** exact callback input count and
    bounded status/register reads use a dedicated descriptor, inspect bytes only for status 1,
    expose oversized lengths without copying, and reject views. Genuine callback scenes are covered
    by the next completed slice; strict UInt64 decoding is covered by task 15.
14. **NEAR-PROMISE-THEN-1 (wsm-near-promise-then-001 done):** one static child call creates a
    `promise_batch_then` self callback with independent bounded input/deposit/gas, returns the
    callback receipt after state persistence, and exercises genuine success/failure/oversized
    dependency results.
15. **NEAR-PROMISE-CODEC/PRIVATE-1 (wsm-near-promise-codec/private-001 done):** strict Borsh UInt64
    decoding requires successful exact eight-byte results, and callback bodies authenticate full
    predecessor/current AccountId equality before any dependency read or state write.
16. **NEAR-PROMISE-TRANSFER-1 (wsm-near-promise-transfer-001 done):** static detached/returned native
    transfers stage exact lossless-u128 amounts through the arena, append the transfer action to a
    concrete batch, distinguish return linkage explicitly, and pin exact sandbox balance deltas and
    synchronous insufficient-balance rollback.
17. **NEAR-PROMISE-AND-1 (wsm-near-promise-and-001 done):** two ordered static child calls stage
    their concrete indices in one aligned arena span, immediately form `promise_and`, feed that
    joint dependency to one authenticated self callback, and return only the callback receipt.
    Success plus either one-sided failure pin result order and non-short-circuiting callback reads.
18. **NEAR-INIT-1 (wsm-near-init-001 done):** generated initializers decode arguments, reject the
    reserved `STATE` marker or any pre-marker scalar state, persist scalar fields, then write the
    marker. Repeated sandbox initialization fails without changing the first state; Borsh state
    layout, `ignore_state`, and migration/version policy remain absent.
19. **NEAR-PAYABLE-1 (wsm-near-payable-001 done):** initializers and mutating entries reject either
    nonzero attached-deposit word before decoding input, while views emit no guard and methods that
    explicitly observe `Context.attachedDeposit` accept the full u128 value. Donation-only payable
    methods are covered by the following explicit policy slice.
20. **NEAR-ENTRY-POLICY-1 (wsm-near-entry-policy-001 done):** `pf_near_private` and
    `pf_near_payable` survive extraction only as NEAR-owned metadata, participate in the canonical
    digest, and generate wrappers in official private → non-payable → input order. Private compares
    the full predecessor/current AccountId and panics with the exact method-specific message;
    explicit payable admits donation-only mutators while payable views fail at lowering.
21. **NEAR-UNINITIALIZED-1 (wsm-near-uninitialized-001 done):** every ordinary state-consuming
    wrapper requires the canonical `STATE` marker after private/non-payable/input handling and
    before scalar field or callback-result reads. Missing state uses exact `PanicOnDefault` text and
    never creates implicit zero state. This is ProofForge's explicit-initializer policy: official
    near-sdk-rs `unwrap_or_default()` also permits non-panicking `Default` implementations.
22. **NEAR-STATE-ENVELOPE-1 (wsm-near-state-envelope-001 done):** exact
    `PFNRST01 || fnv1a64(schema)_le` metadata binds ordered slot name/width/ABI without binding
    executable methods. Entries distinguish missing from malformed/legacy/foreign schemas using a
    dedicated register and fail closed before state/result reads.
23. **NEAR-MIGRATION-1 (wsm-near-migration-001 done):** an explicitly private, non-payable,
    zero-argument entry dispatches one declared old schema envelope, forbids implicit current-state
    reads, converts explicit old split keys, persists transformed fields, and advances the current
    envelope last. The sandbox gate performs a genuine Counter V1 → two-field V2 code upgrade.

Each task must pin host imports, memory ranges, bounds, view legality, canonical IR, assembly, and a
near-sandbox scene. Mainnet/testnet deployment remains a separate lifecycle gate.
