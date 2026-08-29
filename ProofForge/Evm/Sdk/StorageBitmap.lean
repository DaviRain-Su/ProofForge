import ProofForge.Attr
import ProofForge.Core.Collections
import ProofForge.Evm.Sdk.Storage

namespace ProofForge.Evm.Sdk.StorageBitmap

/-!
# EVM SDK persistent bounded storage bitmap of UInt64 words (R5-015)

`StorageBitmap` is the reusable *persistent* bounded-bitmap policy for EVM storage, comparable
to OpenZeppelin's `BitMaps` library. It binds the shared `Core.Collections.BoundedBitSet`
packed-word semantics to the existing physical state model — exactly the way `StorageVec` binds
`Core.Value.BoundedVec`:

- **compile-time bit capacity**: the backing store is an ordinary
  `Vector UInt64 (wordCount bits)` field of the consumer's `State` structure, flattened by the
  existing fixed-vector extraction path into `wordCount bits = (bits + 63) / 64` consecutive
  static slots (`words_0 …`). There is no runtime slot allocator, no hashed namespace, and no
  pointer; the slot table is fixed at extraction. The bit capacity is compile-time data and
  never appears as runtime state.
- **no runtime length**: every word of the table is live state, matching
  `Core.Collections.BoundedBitSet` (which has no length/header either). The *bit* capacity — not
  a length scalar — is the single bounds authority.
- **checked bit operations**: the pure `pf_inline` helpers below own all index/word/mask policy
  (`inRange`/`wordIndexOf`/`maskOf`/`containsOf`/`setOf`/`clearOf`/`toggleOf`); each bit
  operation checks `index < bits` first, computes `wordIndexOf index = index / 64` and
  `maskOf index = 1 <<< (index % 64)`. Out-of-range indexes fail closed at the consumer's own
  terminal and can never wrap into or alias a lower bit, because the word/mask helpers are only
  reachable behind `inRange`.

## Why policy helpers, not returned bitmaps

The current EVM extraction lowers dynamic-index `Vector` reads/writes only when the vector is a
`State` field and the index proof is an explicit `if h : … < wordCount` hypothesis in the
consumer (`Examples.EvmStaticRoster.setSeat`, `Examples.Lang.setAt`,
`Examples.EvmVecLog.record`). A generic helper returning an updated `Vector UInt64 n` value is
not an extractable shape today, so — exactly like `StorageVec` and `Roles.Set2` — this module
owns the reusable *decisions and word arithmetic* while applications own the literal `State`
field writes:

```lean
if StorageBitmap.inRange capU64 index then
  let w := StorageBitmap.wordIndexOf index
  if h : w.toNat < 2 then                       -- compiler proof for the physical write
    .ok ({ s with flags := s.flags.set w.toNat (StorageBitmap.setOf s.flags[w.toNat] index) h }, 1)
  else
    .error .malformed                           -- unreachable under an admissible decision
else
  .error .oob
```

The inner `else` is unreachable whenever `inRange` drives the branch (`index < bits` implies
`index / 64 < wordCount bits`); mapping it to the application's malformed terminal keeps the
write path honest without duplicating policy.

## Fail-closed policy

| situation | helper result | suggested consumer terminal |
|---|---|---|
| `bits = 0` descriptor | `Descriptor.wellFormed = false` | reject before any extraction is trusted |
| word table length ≠ `wordCount bits` | `Descriptor.wellFormed = false` | reject before any extraction is trusted |
| non-UInt64 or non-array word table | `Descriptor.wellFormed = false` | reject before any extraction is trusted |
| `bits ≤ index` (OOB) | `inRange = false` | typed error / revert, or view fallback |
| OOB word/mask arithmetic | unreachable behind `inRange` | never aliases a lower bit |
| any in-range mutation | word read-modify-write of one slot | O(1), capacity-independent |

## Resource contract (worst case, O(1) in every dimension)

Each bit operation touches exactly *one* storage slot — the selected word — independent of
`bits`; there is no loop over the word table. Distinct-slot footprint:

| operation | distinct slots read | slots written | notes |
|---|---|---|---|
| `containsOf` read (view) | 1 | 0 | selected word slot only |
| set / clear / toggle | 1 | 1 | read-modify-write of the selected word |
| claim-style check-and-set | 1 | 1 | one read gates the one write |

Two honest qualifiers: (1) the word index and mask subexpressions (`div`, `mod`, `shl`) are
recomputed at each use site instead of cached in a Yul local — a constant number of ALU ops,
and the solc optimizer may CSE them; (2) a consumer's own authorization gate adds its own
footprint (e.g. `Access.requireOwner` reads the three Address limbs of the stored owner). Cold
zero→nonzero SSTORE pricing dominates real gas; the SDK guarantees only the *shape* — constant,
capacity-independent slot count, no iteration.

Clear-all / enumeration over the whole bitmap is *out of scope*: zeroing or scanning every
word is a `wordCount bits`-bounded loop, and no such consumer loop is claimed here. Consumers
that need bulk policy must say so explicitly with their own compile-time bounded iteration.

The descriptor is compile-time data erased before extraction and costs nothing at runtime.
-/

/-- Word-table length of a bit capacity; the same packing as
`Core.Collections.BoundedBitSet` so the EVM binding and the logical semantics never disagree on
geometry. -/
@[pf_inline] def wordCount (bits : Nat) : Nat :=
  Core.Collections.bitSetWordCount bits

/-- Compile-time descriptor of one persistent bounded bitmap: exactly the fixed
`Vector UInt64 (wordCount bits)` word-table field in consecutive static slots. There is no
runtime length scalar — the whole table is live state. Handles are extraction-time data erased
before runtime; they never appear in emitted code. -/
structure Descriptor (bits : Nat) where
  /-- Fixed word-table field: flattens to `wordCount bits` consecutive 8-byte slots. -/
  words : Storage.Static.Handle (Vector UInt64 (wordCount bits))
  deriving Repr

/-- Declare the word table as one static field, in the exact position the consumer's `State`
structure declares it. -/
@[pf_inline] def declare (layout : Storage.Static.Layout) (wordsName : String) (bits : Nat) :
    Storage.Static.Allocated (Descriptor bits) :=
  let words := layout.array (α := Vector UInt64 (wordCount bits)) wordsName .u64 (wordCount bits)
  { handle := { words := words.handle }, next := words.next }

/-- Descriptor-level validity, checked by focused tests before any extraction is trusted:
positive codec-representable bit capacity and exactly the declared one-slot-per-word UInt64
array handle of length `wordCount bits`. A zero capacity, a mismatched or zero word table, a
wrong static leaf shape, or a non-UInt64 payload all fail closed here. -/
def Descriptor.wellFormed {bits : Nat} (bitmap : Descriptor bits) : Bool :=
  0 < bits && bits < UInt32.size &&
    bitmap.words.wellFormed &&
    bitmap.words.spec == Storage.Static.Spec.arrayLeaves .u64 (wordCount bits)

/-! ## Runtime policy helpers

All helpers are pure `pf_inline` functions over `UInt64` runtime scalars; `bits` must decode to
a compile-time literal at every call site (consumers expose one `@[pf_inline]` capacity literal
for it), while `index` and the loaded `word` are runtime values. `inRange` is the single bounds
authority: consumers must gate every word/mask use on it, so out-of-range indexes can never
wrap or alias a lower bit. The arithmetic matches `Core.Collections.BoundedBitSet.contains` /
`update?` exactly (`index / 64`, `1 <<< (index % 64)`), so host truth tables are the real
policy semantics and the emitted `div`/`mod`/`shl`/`and`/`or`/`xor`/`not` ops are truthful on
extraction. -/

/-- The single bounds gate shared by every bit operation: `index` names a real bit of the
compile-time capacity. -/
@[pf_inline] def inRange (bits index : UInt64) : Bool :=
  index < bits

/-- Word-table index of a bit: `index / 64`. Meaningful under `inRange`; extraction lowers it
to one `div`, never a loop. -/
@[pf_inline] def wordIndexOf (index : UInt64) : UInt64 :=
  index / 64

/-- Single-bit mask of a bit inside its word: `1 <<< (index % 64)`. Under `inRange` the shift
amount is below 64, so host `UInt64` semantics and EVM `shl` agree exactly. -/
@[pf_inline] def maskOf (index : UInt64) : UInt64 :=
  (1 : UInt64) <<< (index % 64)

/-- Read decision over an already-loaded word: is this bit set? Matches
`BoundedBitSet.contains`'s word test. -/
@[pf_inline] def containsOf (word index : UInt64) : Bool :=
  word &&& maskOf index != 0

/-- Word value after setting the bit; matches `BoundedBitSet.update? … true`. Idempotent:
setting a set bit writes back the same word. -/
@[pf_inline] def setOf (word index : UInt64) : UInt64 :=
  word ||| maskOf index

/-- Word value after clearing the bit; matches `BoundedBitSet.update? … false`. Idempotent:
clearing a clear bit writes back the same word. -/
@[pf_inline] def clearOf (word index : UInt64) : UInt64 :=
  word &&& ~~~(maskOf index)

/-- Word value after toggling the bit. Toggling twice restores the exact original word. -/
@[pf_inline] def toggleOf (word index : UInt64) : UInt64 :=
  word ^^^ maskOf index

end ProofForge.Evm.Sdk.StorageBitmap
