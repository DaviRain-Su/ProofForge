import ProofForge.Svm.AccountStorage
import ProofForge.Svm.Sdk.Transient

/-!
# Invocation-local bounded byte buffer

Target-owned component contract for one source-visible transient byte buffer/writer. Payload
storage comes from the shared official Solana downward bump heap; only pointer/length/capacity
metadata lives in fixed invocation scratch. The source handle contains compile-time capacity only
and is erased before IR.

Exactly one active byte-buffer handle is allowed alongside one active `TransientVec` handle in
this slice; the two components own disjoint stack cells, so their metadata can never alias and
their allocations compose through the same bump position. Byte bounds, inactive/mismatched
handles, capacity overflow, out-of-range byte values (`> 255`), and OOM all fail with explicit
terminal program errors instead of forming a bad pointer.
-/

namespace ProofForge.Svm.TransientBytes

open Sdk.Transient

/-- Deep invocation-only metadata, disjoint from FIFO's `2056..2304` cells and from
`TransientVec`'s `2312..2343` cells. These cells may survive across ordinary component calls but
never across invocations. -/
def pointerStack : Nat := 2344
def lengthStack : Nat := 2352
def capacityStack : Nat := 2360
def activeStack : Nat := 2368

/-- Distinct terminal errors let clients and runtime tests distinguish allocator OOM, bounds/full,
byte-range, and handle-lifetime violations. -/
def oomErrorCode : Nat := 0x1211
def boundsErrorCode : Nat := 0x1212
def stateErrorCode : Nat := 0x1213
def rangeErrorCode : Nat := 0x1214

/-- Deepest stack offset of the 16-byte `SolBytes` descriptor used by `sol_log_data`. Its base is
`r10 - descriptorStack`; the target emitter stores the active payload pointer at `[base + 0]` and
its current length at `[base + 8]`. The descriptor exists only adjacent to syscall emission; the
pointer never enters a source value, generic IR, or account state. The occupied `2377..2392` bytes
are disjoint from FIFO's `2056..2304` and `AccountStorage`'s `2489..4096` deep scratch. -/
def descriptorStack : Nat := 2392

/-- Compiler-erased byte-buffer geometry. Capacity is measured in bytes. -/
structure Config where
  capacity : Nat
  deriving BEq, Repr, Inhabited

def Config.fixedVec (config : Config) : FixedVec :=
  { buffer :=
      { name := "transientBytes"
        capacityBytes := config.capacity
        alignment := 1
        frameBytes := ProofForge.Svm.Heap.defaultFrameBytes }
    elementBytes := 1
    capacity := config.capacity }

def Config.wellFormed (config : Config) : Bool :=
  config.fixedVec.wellFormed

/-- Static precondition for one fixed-width little-endian append: the completed record must be
representable inside this buffer. -/
def Config.fitsLe64 (config : Config) : Bool :=
  8 ≤ config.capacity

inductive Query where
  | length (config : Config)
  | get (config : Config)
  | pop (config : Config)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .length _ => 0
  | .get _ => 1
  | .pop _ => 0

def Query.effects (_query : Query) : AccountStorage.EffectSummary := {}

def Query.wellFormed : Query → Bool
  | .length config | .get config | .pop config => config.wellFormed

def Query.needsWalk (_query : Query) : Bool := false

def Query.minAccounts (measure : V → Nat) (operands : Array V) (_query : Query) : Nat :=
  operands.foldl (init := 0) fun current value => Nat.max current (measure value)

def Query.canonical (renderValue : V → String) (operands : Array V) : Query → String
  | .length config => s!"tbyte.len.{config.capacity}"
  | .get config =>
      let suffix := String.intercalate "," (operands.map renderValue).toList
      s!"tbyte.get.{config.capacity}({suffix})"
  | .pop config => s!"tbyte.pop.{config.capacity}"

inductive Call (V : Type) where
  | begin (config : Config)
  | push (config : Config) (byte : V)
  | appendLe64 (config : Config) (value : V)
  | set (config : Config) (index byte : V)
  | clear (config : Config)
  | finish (config : Config)
  | logData (config : Config)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .begin config => .begin config
  | .push config byte => .push config (mapValue byte)
  | .appendLe64 config value => .appendLe64 config (mapValue value)
  | .set config index byte => .set config (mapValue index) (mapValue byte)
  | .clear config => .clear config
  | .finish config => .finish config
  | .logData config => .logData config

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .begin config => return .begin config
  | .push config byte => return .push config (← mapValue byte)
  | .appendLe64 config value => return .appendLe64 config (← mapValue value)
  | .set config index byte => return .set config (← mapValue index) (← mapValue byte)
  | .clear config => return .clear config
  | .finish config => return .finish config
  | .logData config => return .logData config

def Call.values : Call V → Array V
  | .begin _ | .clear _ | .finish _ | .logData _ => #[]
  | .push _ byte | .appendLe64 _ byte => #[byte]
  | .set _ index byte => #[index, byte]

def Call.effects (_call : Call V) : AccountStorage.EffectSummary := {}

def Call.minAccounts (measure : V → Nat) (call : Call V) : Nat :=
  call.values.foldl (init := 0) fun current value => Nat.max current (measure value)

def Call.wellFormed (valueWellFormed : V → Bool) : Call V → Bool
  | .begin config | .clear config | .finish config | .logData config => config.wellFormed
  | .push config byte => config.wellFormed && valueWellFormed byte
  | .appendLe64 config value => config.wellFormed && config.fitsLe64 && valueWellFormed value
  | .set config index byte =>
      config.wellFormed && valueWellFormed index && valueWellFormed byte

def Call.canonical (renderValue : V → String) : Call V → String
  | .begin config => s!"tbyte.begin.{config.capacity}"
  | .push config byte => s!"tbyte.push.{config.capacity}({renderValue byte})"
  | .appendLe64 config value => s!"tbyte.appendLe64.{config.capacity}({renderValue value})"
  | .set config index byte =>
      s!"tbyte.set.{config.capacity}({renderValue index},{renderValue byte})"
  | .clear config => s!"tbyte.clear.{config.capacity}"
  | .finish config => s!"tbyte.finish.{config.capacity}"
  | .logData config => s!"tbyte.logData.{config.capacity}"

end ProofForge.Svm.TransientBytes
