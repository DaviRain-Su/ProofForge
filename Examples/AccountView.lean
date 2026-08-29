import ProofForge

namespace Examples.AccountView

open ProofForge.Svm.Sdk

/--
Application fixture for the SVM-RT-1 bounded remaining-account view. State account 0 is
authenticated ProofForge state; the compile-time `window` handle names physical accounts 1..4 once
and every entry selects one of them by a runtime index. The target validates the index against the
compile-time capacity and the available account count and fails atomically with `Custom(1)`
outside the window, before any state store.
-/
structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- 2^64 - 1。Lean 4.31 无 `UInt64.max`。 -/
def u64Max : UInt64 := ~~~(0 : UInt64)

/-- One compile-time window: physical accounts 1..4, indexed by a runtime number. -/
@[pf_inline] def window : Account.View := Account.View.bounded 1 4

/-- Two fixed spans in the first remaining account. Unlike `window`, these descriptors are
compile-time byte geometry for official program-memory host functions. -/
@[pf_inline] private def firstPrefix : Memory.Span := Memory.Span.accountData 1 0 8
@[pf_inline] private def secondPrefix : Memory.Span := Memory.Span.accountData 1 8 8

@[pf_entry]
def init (initial : UInt64) : State :=
  { value := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

/-- First data word of remaining account `1 + index`. -/
@[pf_entry]
def peek (_s : State) (index : UInt64) : UInt64 :=
  window.peekData 0 index

/-- Second data word of remaining account `1 + index`. -/
@[pf_entry]
def peekWord1 (_s : State) (index : UInt64) : UInt64 :=
  window.peekData 1 index

/-- Public-key word 0 of remaining account `1 + index`. -/
@[pf_entry]
def peekKey (_s : State) (index : UInt64) : UInt64 :=
  window.peekKey 0 index

/-- `is_signer` flag of remaining account `1 + index`. -/
@[pf_entry]
def peekSigner (_s : State) (index : UInt64) : UInt64 :=
  window.peekSigner index

/-- `is_writable` flag of remaining account `1 + index`. -/
@[pf_entry]
def peekWritable (_s : State) (index : UInt64) : UInt64 :=
  window.peekWritable index

/-- `data_len` of remaining account `1 + index`. -/
@[pf_entry]
def peekDataLen (_s : State) (index : UInt64) : UInt64 :=
  window.peekDataLen index

/-- Lamports of remaining account `1 + index`. -/
@[pf_entry]
def peekLamports (_s : State) (index : UInt64) : UInt64 :=
  window.peekLamports index

/-- Whether remaining account `1 + index` is owned by the current program. -/
@[pf_entry]
def peekOwned (_s : State) (index : UInt64) : UInt64 :=
  window.ownedBySelf index

/-- Compare two fixed prefixes without copying account bytes into a source-visible buffer. -/
@[pf_entry]
def comparePrefixes (_s : State) : UInt64 :=
  Memory.compareI32Bits firstPrefix secondPrefix

/--
Absorb the selected account's first data word plus `delta` into the state cell. The view read is
validated by the target before the checked add and the state store, so an out-of-window index
leaves the committed state byte-identical.
-/
@[pf_entry]
def absorb (s : State) (index delta : UInt64) : Except Error (State × UInt64) :=
  if s.value ≤ u64Max - delta then
    let loaded := window.peekData 0 index
    let next := s.value + delta + loaded
    .ok ({ value := next }, next)
  else
    .error .overflow

end Examples.AccountView
