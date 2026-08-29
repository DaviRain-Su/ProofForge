# Runtime / SDK capability matrix

> Ownership freeze: 2026-08-27. This matrix records the current source surface and the owner of
> every lowering boundary. It is descriptive, not a promise that unsupported rows are available.
> 当前实现与 Solana SDK / Solidity + OpenZeppelin 的完整差距和优先级另见
> [mainstream parity baseline](mainstream-parity.md)。

## 1. Rules

The reusable language is ordinary Lean 4 plus stable target SDK facades. Runtime, Component, and
Emit are implementation boundaries, not three alternative application APIs.

```diagram
┌────────────────────┐
│ Examples / contract│  protocol policy, concrete layout, business validation
└─────────┬──────────┘
          ▼
┌────────────────────┐
│ target SDK / Source│  typed handles, bounded containers, closed effects
└─────────┬──────────┘
          ▼
┌────────────────────┐
│ Component bridge   │  static shape, operands, effects, resource contract
└─────────┬──────────┘
          ▼
┌────────────────────┐
│ target Runtime/Emit│  ABI, syscalls/opcodes, physical bytes/slots
└────────────────────┘
```

- Shared Lean/Profile/Extract/Core owns values, schemas, checked control, bounded loops, and CFG.
  It does not own account geometry, EVM slots, syscalls, opcodes, or protocol rules.
- SVM persistent state is account bytes. A handle contains compile-time account/word/stride/
  capacity/index-base/access metadata; a stored value is a scalar offset/index, never a VM pointer.
- SVM scratch is invocation-local and bounded. The official-shaped bump heap defaults to 32 KiB,
  may be configured up to 256 KiB by the VM, does not reclaim on `dealloc`, and cannot back a
  persistent `Map` or `Vec`.
- EVM persistent state is static slots or typed hashed namespaces. `Storage.Layout` allocates
  handles at extraction time and is never materialized in contract storage.
- Applications may own offsets, selectors, event variants, matching/fee rules, and wire choices,
  but must bind them once into typed descriptors. They must not import a target `Emit` module or
  duplicate emitter/runtime recipes.
- A new Queue/Map/Allocator/codec is a source/SDK composition unless it requires a genuinely new
  VM effect. Ops/IR/Emit expansion is the last option, not the default implementation technique.

## 2. Shared language

| Source capability | Owner | Lowering/effect | Physical state | Current status / fail-closed edge |
|---|---|---|---|---|
| `@[pf_entry]`, structures, fixed `Vector`, bounded enum/option | Profile + Extract + Core Schema | typed leaves and explicit CFG writes | target chooses account offsets or storage slots | Available for current fixed scalar shapes; recursive/unbounded data and general `Array` fail closed |
| checked `UInt8/16/32/64`, Bool, comparisons, bounded `for` | Core Ops/CFG | target-neutral value/control nodes | target registers scalar representation | Available; general recursion, `IO`, FFI, and unbounded loops fail closed |
| invocation-local scalar tuples/frames | Extract + Core CFG | locals and fixed-loop frame snapshots | SVM stack / EVM Yul locals | Available for bounded scalar state; not a heap/container or persistent state |
| typed bool/uint/address/fixed-bytes metadata; bounded unit/tuple/record/enum/option/array codec shape; allocation-free `UInt128`/`UInt256`/`FixedBytes n` values; compiler-erased `BoundedVec α capacity` input carrier and capacity-preserving operations | `Core.Codec` + `Core.Value` + Extract | target adapter selects Borsh or ABI; descriptor validation owns depth/node/leaf/capacity budgets; scalar runtime-index reads become bounded target-local selects | fixed logical limbs or fixed extracted scalar frame; no shared wire/account/storage layout | Literal Lean tuple/record/enum/option/Vector schemas and scalar target bindings are available; SVM/EVM independently bind static aggregates, tagged inputs, bounded variable inputs, and scalar dynamic reads. `BoundedVec`'s host Vector does not survive extraction. Wide/aggregate dynamic elements, mutation writeback, recursive/polymorphic/malformed/over-budget shapes fail closed |
| bounded enumerable Map/Set logical semantics | `Core.Collections` | fixed-capacity scan plus reject/replace/swap-remove laws; no target lowering in this slice | shared model has no physical persistence; SVM account RBMap/allocator and EVM hashed/static storage remain separate | Available as a deterministic host/source semantic contract with malformed/full/duplicate/missing outcomes. No HashMap/Array/pointer/allocator or observable iteration order. Target binding remains fail closed until separately qualified |
| bounded Queue/BitSet logical semantics | `Core.Collections` | fixed-capacity ring laws and packed fixed-word membership/update; no target lowering in this slice | shared model has no physical persistence; SVM account bytes and EVM fixed/hashed slots remain separate | Available with checked full/empty/OOB/malformed outcomes, canonical empty queue, exact bit word count, and no allocation/pointer. Target binding remains fail closed until separately qualified |
| bounded bytes / UTF-8 string logical semantics | `Core.Value` + `Core.Collections` + `Core.Codec` | fixed UInt8 frame, checked active length, reused BoundedVec laws, strict Unicode-scalar UTF-8 validation | no shared wire, account, storage, heap object, or pointer | Literal capacities and resource accounting reach Extract with distinct bytes/string schemas. SVM Borsh and EVM standard ABI independently bind inputs and top-level bounded outputs, each with an output-side UTF-8 gate. Dynamic capacities, zero/over-budget descriptors, tagged/nested dynamics, and wide dynamic elements fail closed |

## 3. SVM

| Source/API surface | Owner | Component bridge | Target effect | Physical state/resource | Current status / fail-closed edge |
|---|---|---|---|---|---|
| account key/owner/length/flags and return data | `Svm.Runtime` | direct target query | Loader-v3 account/return-data access | invocation account headers and checked account bytes | Static account indexes available; runtime-selected remaining-account reads use the bounded `Svm.AccountView` row below |
| Clock, EpochSchedule, compile-time Rent | `Svm.Sysvar` + `Svm.Sdk.Sysvar` | `Component.sysvar` | fixed `sol_get_clock_sysvar` / `sol_get_epoch_schedule_sysvar` / `sol_get_rent_sysvar` query interpreter | one fixed deep-stack native sysvar copy; no account effect, allocation, pointer, or persistent state | Available (`R2-007/008`): all unsigned/Boolean Clock/EpochSchedule fields use exact native offsets, including EpochSchedule's 40-byte C layout rather than its 33-byte packed layout. Production source adds no top-level Ops/IR/main-Emit cases; historical Golden constructors delegate to the same interpreter. Signed timestamps, sliced generic sysvars, and runtime-selected Rent geometry remain fail closed |
| bounded remaining-account view, runtime-safe index, read-only header/data gate | `Svm.AccountView` + `Svm.Sdk.Account.View` | `Component.accountView` | index validated against compile-time capacity and runtime `NUM_ACCOUNTS`, bounded runtime account-count walk, checked header/data read | compile-time `base`/`capacity` window over fixed account headers; read-only, no pointers, no scratch | Available (`R2-001`/`R3-002`); window OOB, available-count OOB, duplicate-key `NON_DUP_MARKER`, and short data fail atomically with `Custom(1)`; writes and runtime geometry fail closed |
| official program-memory spans | `Svm.Memory` + `Svm.Sdk.Memory` | `Component.memory` | one checked `sol_memcpy_` / `sol_memmove_` / `sol_memcmp_` / `sol_memset_` call | compile-time account/offset/length; transient pointer exists only across the syscall | Available (`R2-005`): actual length always checked; writes require writable + current-program owner; memcpy overlap and malformed spans fail closed. Pointer arithmetic, dynamic account spans, and persistent pointers remain unavailable |
| invocation-local bounded `Vector64` | `Svm.TransientVec` + `Svm.Sdk.Transient.Vector64` | `Component.transientVec` | begin/push/set/clear/finish effects plus length/get/pop queries, backed by shared official-shaped downward bump emission | fixed `capacity × 8` heap payload, scalar invocation metadata, one active handle; no source-visible address | Available (`R3-012`/`R3-017`): full/OOB/empty-pop is `0x1202`, inactive or mismatched capacity is `0x1203`, OOM is `0x1201`; finish closes without reclaiming. Multiple active vectors, generic elements, insert/remove-at/iteration, and persistent pointers remain fail closed |
| invocation-local bounded bytes | `Svm.TransientBytes` + `Svm.Sdk.Transient.Bytes` | `Component.transientBytes` | begin/push/set/clear/finish/log-data effects plus length/get/pop queries and fixed little-endian append | fixed byte-capacity heap payload, scalar invocation metadata, one active handle alongside one Vector64; no source-visible address | Available (`R3-013`/`R3-016`/`R3-018`): full/OOB/empty-pop=`0x1212`, stale/mismatch=`0x1213`, byte range=`0x1214`, OOM=`0x1211`; no reclaim/realloc. Same-type multiple handles, insert/remove-at/iteration, runtime strings, and persistent pointers fail closed |
| PDA seeds, canonical program ids, SPL base-state views, System/Token/ATA/Memo wrappers, generic CPI words | `Svm.Runtime` + `Svm.Sdk.Pubkey` + `.Program` + `.Pda` + `.System` + `.Token` + `.AssociatedToken` + `.Memo` + `Svm.Ops.invoke` + `Svm.Scratch` | existing account queries plus target invoke effect | executable/full-key/owner/data-word gates, typed bounded instruction plan, `sol_invoke_signed_c` | fixed account headers/bytes and 1,024-byte CPI stack bank; compile-time descriptors and invocation-only scratch | Static ASCII PDA, System, classic Token, role-typed ATA and bounded ASCII Memo have compiler-erased SDK names (`R3-004..011`). Canonical System/Token/Token-2022/ATA/Memo ids and exact 82/165-byte Token base views validate complete keys, owner, state/tags and unaligned fields without allocation (`R3-011`). ATA still receives caller-selected programs; applications explicitly select classic or Token-2022 flavor. Dynamic signed self-CPI composes existing scratch plans. Runtime-selected Memo/account geometry and real Token-2022 extension semantics remain unavailable/fail closed |
| `Region`, `Field`, scalar/fixed-record read/write | `Svm.AccountStorage` + `.Source` | `Component.accountStorage` | checked load/store | fixed account bytes with explicit zero/one-based index | Available; runtime geometry, account heap objects, OOB and unauthorized writes fail closed |
| key4 and ordered-pair RB maps, allocator, cursor, insert/remove/update | `Svm.AccountStorage` + `.Source` | `Component.accountStorage` | bounded in-place tree/allocator routines | fixed stride/capacity, one-based slots, `0` sentinel | Available for current key4/two-word schemas; arbitrary key/value shapes, hash maps, unbounded traversal and full-book policy fail closed |
| whole-side FIFO cancellation and bounded cancel-up-to | `Svm.FifoCancel` + `.Source` | `Component.fifoCancel` | cursor + validated map mutation + collateral fold | account map plus invocation-local scalar cells | Available for statically described ordered sides; protocol selection and event schema remain application-owned |
| bounded begin/append/finish event batching | `Svm.BatchRecorder` + `.Source` | `Component.batchRecorder` | heap-backed byte writer + signed self-CPI | max 1,246-byte payload, fixed record bound, invocation-local pointer | Available; over-capacity flushes before append and malformed config fails closed; no pointer enters account state |
| packed/Borsh entry and return plans | `Svm.EntryAdapter` | entry adapter bridge | checked instruction-data decode and return encoding | bounded invocation bytes and fixed scalar locals | Typed scalars plus static record/product/fixed-vector raw parameters derive exact little-endian cursor/local plans and canonical Bool guards; Option/payload enums use canonical u8 tags; `BoundedVec`, bytes, and String inputs use canonical u32 length with fixed-capacity zeroed locals. Independent output plans return top-level one-limb bounded arrays/bytes/String and tagged Option/enums as canonical active prefixes, with output-side strict UTF-8 and disjoint staging. Nested/constructed/wide dynamic returns, richer payloads, and generated aggregate ABI remain fail closed |
| transient allocator model | `Svm.Heap` + `Svm.Heap.Emit` + `Svm.Sdk.Transient` | BatchRecorder, transient Vector64, and signed-CPI consumers | one official-shaped downward bump implementation plus composed fixed scratch plans | invocation-local 32 KiB default, 256 KiB VM ceiling; fixed 1,024-byte CPI bank | Bounded descriptors expose alignment, capacity, frame, exact-fit and OOM; BatchRecorder and Vector64 share allocator emission while signed CPI reuses `Scratch.Plan`. Deallocation is a no-op and no persistent pointer crosses the invocation boundary (`R3-003`/`R3-012`) |
| unified `Svm.Sdk` facade | `Svm.Sdk.Account` + `.Pubkey` + `.Program` + `.Pda` + `.System` + `.Token` + `.AssociatedToken` + `.Memo` + `.Storage` + `.Queue` + `.Transient` + `.Memory` | composes existing Runtime leaves, AccountView, `AccountStorage.Source`, Heap/Scratch, memory spans, and target components | fixed/bounded read gates, canonical identity/base-state policy, static/fixed-account CPI facades, checked storage/tree/allocator/memory routines, and transient bounded mutation; no new recipe opcode | compile-time physical/CPI-relative account handles, key words, windows/seeds/payloads, fixed account words with one-based indexes/`0` sentinels, or invocation-local bounded memory | Fixed Account/Signer/view, canonical program identities, exact SPL base views, static PDA/System/Token/ATA/Memo effects, compile-time-space rent-exempt regular/seeded/PDA create, persistent Field/Vec/Queue/Map/RBMap/allocator, checked account-memory spans, and transient buffer/Vector64/writer/codec contracts have independent consumers. Multiple active/generic transient collections, runtime-selected Memo/account geometry, rent-aware resize/close, and Token-2022 extension semantics remain R3 work |

The old low-level `accData*` names remain compatibility decoding inputs. They are not a license to
add another protocol-shaped intrinsic. New persistent-container code should prefer `Svm.Sdk` typed
handles; its descriptors bind geometry once and erase to the existing generic component effects.
R2/R3 continue narrowing direct Runtime leaves and add bounded transient Scratch rather than
teaching Emit another recipe.

## 4. EVM

| Source/API surface | Owner | Component bridge | Target effect | Physical state/resource | Current status / fail-closed edge |
|---|---|---|---|---|---|
| typed ABI scalar/aggregate metadata, `Address`, shared `UInt128`/`UInt256`/`FixedBytes n`, Context, Immutable | `Core.Codec` + `Core.Value` + `Evm.Codec` + `Evm.Sdk` | `wideWord` where multi-limb logic is required | typed selector/calldata guard/ABI plus environment and checked packed operations | Yul stack/bounded memory; no persistent SDK object | Selector, canonical leaf guards, return packing, and structured ABI JSON consume typed metadata; nested static tuple/record/fixed-array parameters and results are available. Tagged Tuple v1 binds Option/payload-enum inputs and top-level one-limb outputs. `DynamicInputPlan` binds Bounded Array v1 `T[]` and Packed Bytes v1 `bytes`/`string` to canonical contiguous tails, ≤64-word fixed zeroed frames, and exact calldata. Independent `OutputPlan` variants publish canonical bounded arrays/bytes/String and fixed tagged tuples, with zero/inactive-lane checks and output-side strict UTF-8. `UInt256` has checked arithmetic/comparison/bitwise/shift/div/mod. Nested/constructed/wide dynamic returns, dynamic constructors, nested inputs, and unbounded arrays remain fail closed |
| full-width environment observations | `Evm.Sdk.Context` + `Evm.Sdk.Address` + `Evm.Environment` | `Component.environment` | GAS/GASPRICE/BASEFEE/PREVRANDAO/GASLIMIT/BLOBBASEFEE/BLOBHASH/ORIGIN/COINBASE/BLOCKHASH/BALANCE/EXTCODESIZE/EXTCODEHASH plus fixed `msg.sig` and exact `msg.data.length`, with one cached observation per wide/fixed-byte result | EVM transaction/call/block/blob context; scalar stack projections plus one fixed 32-byte address packing scratch word | Available (`R4-006/008..015`, `R5-011`): `UInt256` observations and full `Address` values never truncate to an implicit UInt64; blob base fee remains numeric UInt256 while versioned blob hashes remain source-order `Bytes32`, and absent indices preserve EVM zero. `Context.selector` remains source-order `Bytes4`, not a numeric selector, while `Context.calldataSize` exposes only the protocol-bounded length and no raw bytes/pointer. Origin is exposed but documented as unsuitable in place of caller authorization. BLOCKHASH accepts a checked UInt64 height and preserves the VM's recent-256-block semantics. `Address.codeSize` is UInt64, `Address.codeHash` is source-order `Bytes32`, and `Address.hasCode` honestly means only `EXTCODESIZE != 0` at the observation point; it is not an EOA/authentication or call-success test. No allocation, storage, call, top-level Ops constructor, or main-emitter recipe. Blob payload access, a bounded raw `msg.data` byte view, raw code bytes, and a full UInt256 block-number input remain fail closed |
| static scalar/record/fixed-array declarations plus typed address/address-pair maps | `Evm.Sdk.Storage.Static` + `Evm.StaticStorage` + `Evm.Sdk.Storage` + `Evm.HashedMap` | ordinary State extraction; `Component.staticStorage` for ordered UInt64 writes; `Component.hashedMap` for maps | final static `sload`/`sstore`, ordered schema-resolved `sstore`, typed hash namespace | two disjoint compile-time cursors; descriptors never enter runtime storage | Available (`R5-002`/`R4-005`): Bool/u8/u16/u32/u64, Address, UInt256/Bytes32, flat records, fixed arrays and record arrays validate exact consecutive slots. `Handle UInt64.storeNow` preserves lexical order around CALL and rejects dynamic/unknown/non-8-byte fields without exposing slots. Static declarations do not move hashed-map bases; generic handle reads/writes and runtime allocation remain unavailable |
| Ether, Event, Revert, receive/payable | `Evm.Sdk.Payments` + `Evm.Sdk` + `Evm.NativeFx` | `Component.nativeFx` plus generic source `.errorNamed` ABI derivation | CALL value, LOG, revert, receive | EVM call frame/log/storage effects | Closed Ether accept/send/receive is consumed through the SDK by Vault and TipJar (`R5-005`); source enum zero-argument errors automatically receive matching ABI metadata (`R4-007`). Parameterized generic event/error recipes and hidden state writes fail closed. Reentrancy protection is never inferred from a call: consumers explicitly compose `Sdk.Reentrancy` (`R5-009`) |
| ERC-20/WETH/router/permit interaction | `Evm.Sdk.Payments` + `Evm.Sdk.Effect` + `Evm.ClosedCall` + `Evm.CallResult` | `Component.closedCall` | typed closed CALL/STATICCALL and one shared result interpreter | closed calldata; ≤32 copied returndata bytes at memory offset zero | Available (`R4-001`/`R5-005`/`R5-012`): ERC-20 mutation requires CALL success plus exact 32-byte canonical `1`, or empty returndata from a target with post-call runtime code; false, word `2`, other lengths, and no-code empty fail closed. Success-only calls accept nonempty ignored data or code-backed empty; exact-word reads remain exact 32. `Effect.thenTrue` sequences an effect carrier into a canonical Bool, and CFG keeps explicit source results distinct from mutation carriers. Exact-32 is stricter than OpenZeppelin's ≥32 compatibility branch. Callee/calldata remain closed; arbitrary call, delegatecall, proxy, create, revert bubbling, and unbounded returndata fail closed |
| reusable contract policy (access, roles, pause, reentrancy, token/NFT ledgers, persistent collections) | `Evm.Sdk.Access` + `.Roles` + `.Pausable` + `.Reentrancy` + `.Fungible` + `.Erc721` + `.StorageVec` | composition of static/ordered-static/hashed-map/native/closed-call components | explicit source calls to reads/writes/logs/reverts | fixed Address/scalar fields, typed static declarations, and compile-time hashed namespaces | Access, capacity-2 roles and Pausable own pure gates/transitions (`R5-001/003/004`). `Reentrancy` composes explicit UInt64 handles with ordered enter/leave around application-owned calls; two consumers and a hostile callback prove nested rejection/rollback (`R5-009`). Balances/Allowances own checked O(1) fungible movement (`R5-006..008`). `Erc721` owns bounded O(1) owner/approval/operator/balance policy over compile-time map handles, rejects token ids outside its 192-bit key envelope before truncation, and is consumed by Collectible/Badge (`R5-013`). `StorageVec` owns the persistent bounded UInt64 vector contract — compile-time capacity, explicit length, checked active-prefix decisions, visible literal field writes, O(1) documented gas shape — consumed independently by EvmVecLog and EvmVecStack (`R5-010`). Dynamic roles/indexed Address returns, typed standard asset events, ERC-721 receiver/full-width-id semantics, bounded ERC-1155, and richer storage-vector elements remain fail closed |

EVM does not consume `Svm.AccountStorage`, account indexes, one-based allocators, or the SVM heap.
SVM does not consume EVM slot cursors or hashed-map namespaces. Shared semantics can have two
bindings, but the physical storage descriptor is always target-owned.

## 5. Application boundary

| Application | Owns | Must consume | Must not create |
|---|---|---|---|
| `Examples.Phoenix*` | market/account layout, order comparison, crossing, fees, TIF/self-trade/funds policy, official wire and audit choices | SVM typed account storage, allocator/map/cursor, recorder, entry adapter, CPI/PDA/Token capabilities | Phoenix-named Ops/IR/Emit cases, heap-backed persistent books, pointers in accounts |
| `Examples.Token`, `Examples.Capped`, `Examples.TwoStepCounter`, `Examples.Credits`, future EVM contracts | token/cap/access business policy and public ABI | `Evm.Sdk` typed storage/context/event/revert/closed calls and reusable Access/Pausable/Fungible policy | numeric map bases, hand-built topics/selectors, stale-nominee maps, SVM account geometry |
| future cross-target examples | shared behavioral fixture only | separate SVM and EVM state/ABI bindings | a fake unified storage abstraction |

Registry and historical golden fixtures may name applications because they enumerate build/test
artifacts. Production target Runtime/Component/Emit modules may not import applications or contain
application protocol vocabulary.

## 6. Enforced gates

`python3 scripts/check_ownership.py` runs in CI and enforces the source-level freeze:

1. `Examples/**/*.lean` cannot directly import any `ProofForge.Svm.*.Emit` or
   `ProofForge.Evm.*.Emit` module.
2. Production SVM/EVM target modules cannot import `Examples` or `Projects`.
3. Production target modules (registries excluded) cannot contain Phoenix protocol vocabulary.

The gate deliberately does not pretend that the current umbrella import is the final SDK surface.
R3 narrows SVM applications to `Svm.Sdk`; R5 continues narrowing EVM contracts to `Evm.Sdk`.
Canonical IR/layout tests remain responsible for proving that a facade erases to the same generic
component operations and does not smuggle numeric layout policy into Emit.
