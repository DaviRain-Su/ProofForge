import ProofForge.Attr
import ProofForge.Svm.Sdk.Queue

/-!
固定容量售票队列。用通用 `Svm.Sdk.Queue` ring FIFO、`Svm.Sdk.Storage` 的 POD
字段列和 key4 有序映射组合出一个非 Phoenix 的小程序。所有持久值都是账户字偏移
和 one-based 槽位下标；`0` 是空哨兵。
-/
namespace Examples.TicketLine

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.Queue
open ProofForge.Svm.Sdk.Storage

/-- Compile-time layout for the program-owned storage account at runtime account index `1`.

The extracted `State.dummy` lives in runtime account `0`; no SDK region aliases that source-state
account. Storage-account word 1 is reserved for future layout metadata.

word 2  — queue head header (one-based front slot, `0` = empty)
word 3  — queue count header
words 4..19   — queue payload slots, capacity 16
words 20..35  — per-ticket status POD column, capacity 16
word 40 — registry map root
words 44..331 — registry node-region extent, capacity 16, stride 18; the final owner payload
is word 320 and words 321..331 are static tail padding retained by the full-stride region -/
structure Layout where
  line : BoundedQueue
  status : PodField
  registry : OrderedMap
  owner : PodField
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Layout.line Layout.status Layout.registry Layout.owner

/-- Build the fixed layout for one program-owned storage account. The runtime account index must
become a literal through `pf_inline`; no dynamic account selection or geometry is introduced. -/
@[pf_inline] def small (account : Nat) : Layout :=
  { line := BoundedQueue.oneBased account 2 4 16
    status := { field := Field.oneBased account 20 1 16 }
    registry :=
      { map := RbMap.key4OneBased account 40 44 45 46 18 16 }
    owner := { field := Field.oneBased account 50 18 16 } }

/-- Validate the whole layout with the SDK's own fail-closed geometry predicates. The owner
payload column shares the registry map's one-based node region. -/
def Layout.wellFormed (layout : Layout) : Bool :=
  layout.line.wellFormed && layout.status.wellFormed &&
    layout.registry.wellFormed && layout.owner.wellFormed &&
    layout.owner.field.region.sameShape layout.registry.map.links.region

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- Canonically initialize queue and ordered-map headers in the separate program-owned storage
account. POD payload words need no eager clearing because no header makes them reachable. -/
@[pf_entry]
def initializeStorage (_s : State) : UInt64 :=
  let _ := BoundedQueue.initialize (small 1).line
  OrderedMap.initialize (small 1).registry

/-- Queue views. -/
@[pf_entry]
def lineSize (_s : State) : UInt64 :=
  BoundedQueue.size (small 1).line

@[pf_entry]
def linePeek (_s : State) : UInt64 :=
  BoundedQueue.peek (small 1).line

/-- Zero-based offset from the front across the ring. Empty/OOB returns `0`. -/
@[pf_entry]
def lineGetAt (_s : State) (offset : UInt64) : UInt64 :=
  BoundedQueue.getAt (small 1).line offset

/-- Reset queue headers; payload words stay unreachable. -/
@[pf_entry]
def lineClear (_s : State) : UInt64 :=
  BoundedQueue.clear (small 1).line

/-- Enqueue one ticket; a full line returns the `0` sentinel without mutating state. -/
@[pf_entry]
def lineEnqueue (_s : State) (ticket : UInt64) : UInt64 :=
  BoundedQueue.push (small 1).line ticket

/-- Dequeue the front ticket; an empty line returns the `0` sentinel. -/
@[pf_entry]
def lineDequeue (_s : State) : UInt64 :=
  BoundedQueue.pop (small 1).line

/-- Serve the front ticket as a state transition: an empty line is an explicit overflow.
The dequeue effect is sequenced after the front read; no write result is bound to a local. -/
@[pf_entry]
def serve (_s : State) : Except Error (State × UInt64) :=
  let front := BoundedQueue.peek (small 1).line
  let _ := BoundedQueue.pop (small 1).line
  if front = 0 then .error .overflow else .ok ({ dummy := front }, front)

/-- POD status word for one one-based ticket slot; `0` means unset. -/
@[pf_entry]
def ticketStatus (_s : State) (slot : UInt64) : UInt64 :=
  PodField.readAt (small 1).status slot

/-- Write the status word of one one-based ticket slot. -/
@[pf_entry]
def setTicketStatus (_s : State) (slot value : UInt64) : UInt64 :=
  PodField.writeAt (small 1).status slot value

/-- Register a ticket's owner in the key4 map under key `(ticket, 0, 0, 0)` and store the
owner word in the map-node payload column. Duplicates and exhausted registry capacity are
explicit overflows; success returns the one-based registry slot. The insert result is
discarded rather than bound, and the fresh slot is recovered by lookup. -/
@[pf_entry]
def registerOwner (_s : State) (ticket owner : UInt64) : Except Error (State × UInt64) :=
  let existing := OrderedMap.findKey4 (small 1).registry ticket 0 0 0
  if existing ≠ 0 then .error .overflow
  else
    let _ := OrderedMap.insertKey4 (small 1).registry ticket 0 0 0
    let slot := OrderedMap.findKey4 (small 1).registry ticket 0 0 0
    if slot = 0 then .error .overflow
    else
      let _ := PodField.writeAt (small 1).owner slot owner
      .ok ({ dummy := slot }, slot)

/-- Composed registry lookup: the owner word stored at `(ticket, 0, 0, 0)`, or the `0`
sentinel when the ticket is unregistered. -/
@[pf_entry]
def ownerOf (_s : State) (ticket : UInt64) : UInt64 :=
  OrderedMap.findValueKey4 (small 1).registry (small 1).owner.field ticket 0 0 0

/-- Remove a registry entry. The removal effect is sequenced, then the key is looked up
again: `0` reports both absent and removed, matching the underlying remove contract. -/
@[pf_entry]
def releaseOwner (_s : State) (ticket : UInt64) : UInt64 :=
  let _ := OrderedMap.removeKey4 (small 1).registry ticket 0 0 0
  OrderedMap.findKey4 (small 1).registry ticket 0 0 0

end Examples.TicketLine
