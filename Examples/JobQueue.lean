import ProofForge.Attr
import ProofForge.Svm.Sdk.Storage

/-!
固定容量任务板。用通用 `Svm.Sdk.Storage` facade 组合两个账户驻留容器：
one-based free-list 分配器 + 固定容量 `BoundedVec`。所有持久值都是账户字偏移
和 one-based 槽位下标；`0` 是空哨兵。没有 heap 指针、Lean `Array`/`Map` 或
invocation heap 对象进入持久状态。
-/
namespace Examples.JobQueue

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.Storage

/-- Compile-time account layout for one job board.

word 1  — extracted `State.dummy`; SDK regions never overlap source-state fields
word 2  — live slot count header (allocator occupancy)
word 3  — packed allocator cursor `(bumpIndex | freeListHead <<< 32)`
word 4  — vector count header
words 5..12  — allocator slots, capacity 8, free-list link in slot word 0
words 13..20 — job payload slots, capacity 8 -/
structure Layout where
  allocator : Allocator
  jobs : BoundedVec
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Layout.allocator Layout.jobs

/-- Build the fixed layout for one state account. The account index must become a literal
through `pf_inline`; no runtime account selection or geometry is introduced. -/
@[pf_inline] def small (account : Nat) : Layout :=
  { allocator :=
      { slots :=
          { account, baseWord := 5, strideWords := 1, capacity := 8
            indexBase := .one, access := Access.programOwnedMutable }
        liveCount := Field.scalar account 2
        cursor := Field.scalar account 3 }
    jobs := BoundedVec.oneBased account 4 13 8 }

/-- Validate the whole layout with the SDK's own fail-closed geometry predicates. -/
def Layout.wellFormed (layout : Layout) : Bool :=
  layout.allocator.wellFormed && layout.jobs.wellFormed

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- Allocator views: packed cursor halves are the only allocation state. -/
@[pf_entry]
def slotBumpIndex (_s : State) : UInt64 :=
  Allocator.bumpIndex (small 1).allocator

@[pf_entry]
def slotFreeListHead (_s : State) : UInt64 :=
  Allocator.freeListHead (small 1).allocator

@[pf_entry]
def slotLiveCount (_s : State) : UInt64 :=
  Allocator.liveCount (small 1).allocator

/-- Allocate one one-based job slot; `0` means the fixed capacity is exhausted. -/
@[pf_entry]
def slotAlloc (_s : State) : UInt64 :=
  Allocator.alloc (small 1).allocator

/-- Return a currently allocated slot to the free list. -/
@[pf_entry]
def slotFree (_s : State) (slot : UInt64) : UInt64 :=
  Allocator.free (small 1).allocator slot

/-- Live job count from the vector header. -/
@[pf_entry]
def jobCount (_s : State) : UInt64 :=
  BoundedVec.size (small 1).jobs

/-- Read the job at one-based `position`; out-of-range returns the `0` sentinel. -/
@[pf_entry]
def jobGetAt (_s : State) (position : UInt64) : UInt64 :=
  BoundedVec.getAt (small 1).jobs position

/-- Overwrite the job at one-based `position`; out-of-range performs no store. -/
@[pf_entry]
def jobSetAt (_s : State) (position value : UInt64) : UInt64 :=
  BoundedVec.setAt (small 1).jobs position value

/-- Append one job; a full board returns the `0` sentinel without mutating state. -/
@[pf_entry]
def jobPush (_s : State) (value : UInt64) : UInt64 :=
  BoundedVec.push (small 1).jobs value

/-- Remove the most recent job; an empty board returns the `0` sentinel. -/
@[pf_entry]
def jobPop (_s : State) : UInt64 :=
  BoundedVec.pop (small 1).jobs

/-- Publish one job as a state transition: exhaustion is an explicit overflow, and success
returns the one-based position the job now occupies. -/
@[pf_entry]
def publishJob (_s : State) (value : UInt64) : Except Error (State × UInt64) :=
  let position := BoundedVec.push (small 1).jobs value
  if position = 0 then .error .overflow else .ok ({ dummy := position }, position)

end Examples.JobQueue
