import ProofForge.Attr
import ProofForge.Svm.AccountStorage
import ProofForge.Svm.AccountStorage.Source
import ProofForge.Svm.Sdk.Storage

/-!
# SVM SDK fixed-capacity FIFO queue

A reusable account-resident bounded FIFO composed from `Svm.AccountStorage.Source` checked
load/store stubs. The ring layout and sentinel policy are compile-time descriptor data; the
target emits only the same checked one-based account word accesses that `AccountStorage.Source`
lowers to. No new SVM operation, component, IR constructor, emitter case, native pointer,
Lean `Array`/`Map`, or heap object exists at any point.

## Physical-state contract

- `slots`: a one-based, fixed-stride, fixed-capacity payload region; slot `1..capacity`
  each hold one payload word.
- `head`: scalar header word holding the one-based slot index of the front element, with
  `0` as the empty-queue sentinel.
- `count`: scalar header word holding the live element count `0..capacity`.

The ring successor of slot `h` is `h + 1`, or `1` when `h = capacity`; this is computed with
checked add/sub and a select, never with modulo or unbounded arithmetic. All persistent
values are account offsets/indices; `0` is the universal null sentinel.

## Fail-closed policy

- `pop`/`peek` on an empty queue return `0` and perform no store.
- `push` on a full queue returns `0` and performs no store.
- A stored payload of `0` is indistinguishable from an absent element at the `pop`/`peek`
  boundary; callers that need to distinguish them read `size` first or reserve `0`.
- Malformed conditions (unwritable or foreign account, header or slot beyond `data_len`)
  abort inside the target-owned checked stubs with `Custom(1)`.
-/

namespace ProofForge.Svm.Sdk.Queue

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.AccountStorage.Source
open ProofForge.Svm.Sdk.Storage

/-- Account-resident bounded FIFO ring. The three descriptors are erased at extraction; only
checked account word accesses and scalar header updates remain. -/
structure BoundedQueue where
  slots : Field
  head : Field
  count : Field
  deriving BEq, Repr, Inhabited

attribute [pf_inline] BoundedQueue.slots BoundedQueue.head BoundedQueue.count

/-- Construct a one-word-payload ring with adjacent `head`/`count` scalar headers placed
immediately before the slot body (`headWord`, `headWord + 1`, body at `slotsBaseWord`). -/
@[pf_inline] def BoundedQueue.oneBased
    (account headWord slotsBaseWord capacity : Nat) : BoundedQueue :=
  { slots := Field.oneBased account slotsBaseWord 1 capacity
    head := Field.scalar account headWord
    count := Field.scalar account (headWord + 1) }

/-- Static capacity of the backing region. Compile-time descriptor data, never runtime state. -/
@[pf_inline] def BoundedQueue.capacity (queue : BoundedQueue) : UInt64 :=
  UInt64.ofNat queue.slots.region.capacity

def BoundedQueue.wellFormed (queue : BoundedQueue) (accountLimit : Nat := 64) : Bool :=
  queue.slots.mutableOneBasedWord accountLimit && queue.slots.region.account > 0 &&
    queue.slots.region.capacity ≤ containerCapacityLimit &&
    scalarHeaderWellFormed queue.head queue.slots.region.account accountLimit &&
    scalarHeaderWellFormed queue.count queue.slots.region.account accountLimit &&
    queue.head.firstWord + 1 == queue.count.firstWord &&
    queue.count.firstWord + 1 ≤ queue.slots.firstWord

/-- Live element count from the account-resident header. -/
@[pf_inline] def BoundedQueue.size (queue : BoundedQueue) : UInt64 :=
  read queue.count 0

/-- One-based slot of the front element, or `0` when the queue is empty. -/
@[pf_inline] def BoundedQueue.headSlot (queue : BoundedQueue) : UInt64 :=
  read queue.head 0

/-- Ring successor of one-based slot `h` inside a capacity-`capacity` ring. -/
@[pf_inline] private def nextSlot (slot capacity : UInt64) : UInt64 :=
  if slot = capacity then 1 else slot + 1

/-- Value at the front of the queue, or the `0` sentinel when empty. No store is performed. -/
@[pf_inline] def BoundedQueue.peek (queue : BoundedQueue) : UInt64 :=
  let head := BoundedQueue.headSlot queue
  if head = 0 then 0 else read queue.slots head

/-- Append `value` at the ring tail. A full queue returns `0` and performs no store; success
returns the one-based tail slot that received the value and initializes `head` when the
queue was empty. -/
@[pf_inline] def BoundedQueue.push (queue : BoundedQueue) (value : UInt64) : UInt64 :=
  let size := BoundedQueue.size queue
  if BoundedQueue.capacity queue ≤ size then 0
  else
    let head := BoundedQueue.headSlot queue
    let raw := head + size
    let tail :=
      if head = 0 then 1
      else if BoundedQueue.capacity queue < raw then raw - BoundedQueue.capacity queue
      else raw
    let _ := write queue.slots tail value
    let _ := write queue.count 0 (size + (1 : UInt64))
    let _ := write queue.head 0 (if head = 0 then 1 else head)
    tail

/-- Remove and return the front value. An empty queue returns `0` and performs no store; the
count header shrinks, `head` advances around the ring, and an emptied queue resets `head`
back to the `0` sentinel. The popped slot's payload stays account-resident until the next
push reinitializes it. -/
@[pf_inline] def BoundedQueue.pop (queue : BoundedQueue) : UInt64 :=
  let size := BoundedQueue.size queue
  let head := BoundedQueue.headSlot queue
  if size = 0 || head = 0 then 0
  else
    let value := read queue.slots head
    let remaining := size - (1 : UInt64)
    let _ := write queue.count 0 remaining
    let _ := write queue.head 0
      (if remaining = 0 then 0 else nextSlot head (BoundedQueue.capacity queue))
    value

end ProofForge.Svm.Sdk.Queue