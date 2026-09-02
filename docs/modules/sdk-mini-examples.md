# Non-Phoenix SDK mini-examples (`svm-app-003`)

Four independent Examples consumers prove Queue / Map / BitSet / Versioned reuse
outside Phoenix. Each ships Lean Spec guards, a Registry digest, and Mollusk coverage.

| Component | Example | Mollusk | Spec |
|---|---|---|---|
| Queue (+ OrderedMap) | `Examples.TicketLine` | `runtime-tests/solana/tests/ticket_line.rs` | `Tests/SvmSdkQueueSpec.lean` |
| EnumerableSet (Map-family) | `Examples.UniqueRoster` / `MemberDirectory` | `storage_enumerable_set.rs` | `Tests/SvmSdkStorageEnumerableSetSpec.lean` |
| BitSet | `Examples.FeatureBits` / `ClaimBits` | `storage_bit_set.rs` | `Tests/SvmSdkStorageBitSetSpec.lean` |
| Versioned | `Examples.VersionedLedger` / `VersionedMigrator` | `versioned_codec.rs` | `Tests/SvmVersionedCodecSpec.lean` |

## Build

```bash
lake build Examples.TicketLine Examples.FeatureBits Examples.ClaimBits \
  Examples.UniqueRoster Examples.VersionedLedger
lake exe pf -- build --target svm --out build/sbpf TicketLine
lake exe pf -- build --target svm --out build/sbpf FeatureBits
lake exe pf -- build --target svm --out build/sbpf ClaimBits
lake exe pf -- build --target svm --out build/sbpf UniqueRoster
lake exe pf -- build --target svm --out build/sbpf VersionedLedger
```

## Notes

- TicketLine is the Queue knife and also exercises OrderedMap (registry) + POD columns.
- FeatureBits (idempotent) and ClaimBits (one-shot) share `Sdk.StorageBitSet`.
- UniqueRoster (idempotent) and MemberDirectory (strict) share `Sdk.StorageEnumerableSet`.
- VersionedLedger (no auto-migrate) and VersionedMigrator (explicit edge) share `Sdk.Versioned`.
- Optional Surfpool deploy of one facade is out of this slice; Mollusk is the required gate.
