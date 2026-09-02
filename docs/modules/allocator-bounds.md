# Account-resident allocator vs bounded containers

## Verdict

Having an account-resident allocator does **not** make persistent containers unbounded.
Every map, tree, queue, vector, and freelist still needs a **compile-time capacity** that fits
the account layout. The allocator only recycles one-based slots **inside** that fixed region.

## What the allocator covers

`Sdk.Storage.Allocator` / `OneBasedAllocator` (`ProofForge/Svm/Sdk/Storage.lean`,
`AllocatorModel.lean`) manage:

- bump allocation up to a static `capacity`
- freelist reuse of previously freed one-based indexes
- fail-closed `0` when the live set is full (`capacity ≤ liveCount`)

It does **not**:

- grow the backing account or region at runtime
- invent new geometry after extraction
- bypass Solana account size limits
- replace `BoundedVec` / `BoundedQueue` / `BitSet` fixed capacities

Maps and trees compose the allocator **inside** a fixed node capacity. Exhaustion returns the
null sentinel; callers must still size the region for the worst case they intend to support.

## Solana and SDK ceilings (how to set capacity)

| Bound | Value | Role |
|---|---|---|
| Solana max account data | `Memory.maxAccountDataBytes` = **10 MiB** | Hard ceiling for any single account `data_len` |
| Per-tx resize | `ABI.maxPermittedDataIncrease` = **10240** (`0x2800`) | Max growth of one account in one transaction |
| Loader-v3 program data budget | ≈ 10 MiB − metadata | Program ELF / program-data account room |
| SDK container ceiling | `Storage.containerCapacityLimit` = **65536** | Shared compile-time cap on region capacity (header math / one-based translation); stubs still check real `data_len` |

### Sizing recipe

1. Fix the **record stride** (words or bytes per slot) from the POD / tree node layout.
2. Choose `capacity` so  
   `headerBytes + strideBytes * capacity ≤ accountBytes ≤ 10 MiB`,  
   and the chosen profile is reachable under deploy / resize rules (including +10240 per tx if
   the account starts smaller).
3. Keep `capacity ≤ containerCapacityLimit` (65536) for SDK facades.
4. Prefer protocol-known profiles (e.g. Phoenix seat sizes 512/1024/…) over “max everything”.
5. Treat allocator exhaustion as a normal boundary (`0` / fail-closed), not as a signal to
   grow at runtime.

## Relation to Phoenix / Queue / maps

- Phoenix books and trader registries are **fixed-N** Sokoban layouts; the in-account freelist is
  an allocator over that N, not a dynamic heap.
- `BoundedQueue` / `BoundedVec` stay length-bounded by their region capacity even when an
  allocator freelist exists elsewhere in the same account.
- Transient (`Svm.Heap` / `TransientVec`) memory is invocation-local and unrelated to persistent
  account allocators; never store heap pointers in account state.

## Policy pin

**Still bound after allocator:** yes.  
**Can ignore bounds once allocator exists:** no.  
**Coverage of the allocator:** reuse within a predeclared capacity that already fits Solana’s
per-account and SDK ceilings.
