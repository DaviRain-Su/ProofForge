/-!
# NEAR invocation memory

Checked model for the guest-owned Wasm linear-memory arena. NEAR does not expose malloc/free host
functions: generated contracts own allocation and `memory.grow` is the only backing operation.

The arena is reset at every exported invocation and never reclaims individual allocations. Its
addresses are target-private and must never enter source values or persistent NEAR storage.
-/

namespace ProofForge.Wasm.Near.Memory

def pageBytes : Nat := 64 * 1024

/-- Architectural memory32 ceiling. nearcore currently configures a lower protocol limit; emitted
code observes that limit through `memory.grow == -1` rather than treating it as source policy. -/
def memory32MaxPages : Nat := 64 * 1024

/-- First source-visible consumer bound: at most 32 KiB of fixed UInt64 payload. -/
def maxBuffer64Capacity : Nat := 4096

def alignmentValid (alignment : Nat) : Bool :=
  alignment != 0 && (alignment &&& (alignment - 1)) == 0

def alignUp (address alignment : Nat) : Nat :=
  if alignmentValid alignment then
    let rounded := address + alignment - 1
    rounded - rounded % alignment
  else
    address

def buffer64CapacityValid (capacity : Nat) : Bool :=
  0 < capacity && capacity ≤ maxBuffer64Capacity

structure State where
  base : Nat
  cursor : Nat
  pages : Nat
  maxPages : Nat
  deriving BEq, Repr, Inhabited

def State.wellFormed (state : State) : Bool :=
  0 < state.pages && state.pages ≤ state.maxPages && state.maxPages ≤ memory32MaxPages &&
    state.base ≤ state.cursor && state.cursor ≤ state.pages * pageBytes &&
    state.base % 8 == 0

def initial (base pages maxPages : Nat) : State :=
  { base, cursor := base, pages, maxPages }

/-- Invocation entry rewinds the arena. The emitter also invalidates consumer handles; memory is
not assumed to be zero after a reset. -/
def State.reset (state : State) : State :=
  { state with cursor := state.base }

structure Allocation where
  pointer : Nat
  size : Nat
  alignment : Nat
  deriving BEq, Repr, Inhabited

/-- Checked upward bump allocation with page growth. `none` models malformed geometry, memory32
overflow, or growth beyond the runtime-selected maximum. -/
def allocate (state : State) (size alignment : Nat) : Option (Allocation × State) :=
  if !state.wellFormed || size == 0 || !alignmentValid alignment then
    none
  else
    let pointer := alignUp state.cursor alignment
    let finish := pointer + size
    let requiredPages := (finish + pageBytes - 1) / pageBytes
    if finish > memory32MaxPages * pageBytes || requiredPages > state.maxPages then
      none
    else
      let pages := Nat.max state.pages requiredPages
      some ({ pointer, size, alignment }, { state with cursor := finish, pages })

end ProofForge.Wasm.Near.Memory
