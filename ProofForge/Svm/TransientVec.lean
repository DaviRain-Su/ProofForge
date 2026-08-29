import ProofForge.Svm.AccountStorage
import ProofForge.Svm.Sdk.Transient

/-!
# Invocation-local bounded UInt64 vector

Target-owned component contract for one source-visible transient vector. Payload storage comes
from the official Solana downward bump heap; only pointer/length/capacity metadata lives in fixed
invocation scratch. The source handle contains compile-time capacity only and is erased before IR.

Exactly one transient vector handle is active at a time. Opening another replaces no persistent
state but consumes another non-reclaiming bump allocation. Bounds, inactive/mismatched handles,
capacity overflow, and OOM all fail with explicit program errors instead of forming a bad pointer.
-/

namespace ProofForge.Svm.TransientVec

open Sdk.Transient

/-- Deep invocation-only metadata, disjoint from FIFO's `2056..2304` cells and fixed PDA/sysvar
scratch. These cells may survive across ordinary component calls but never across invocations. -/
def pointerStack : Nat := 2312
def lengthStack : Nat := 2320
def capacityStack : Nat := 2328
def activeStack : Nat := 2336

/-- Distinct terminal errors let clients and runtime tests distinguish allocator OOM, bounds/full,
and handle-lifetime violations. -/
def oomErrorCode : Nat := 0x1201
def boundsErrorCode : Nat := 0x1202
def stateErrorCode : Nat := 0x1203

/-- Compiler-erased vector geometry. Capacity is measured in `UInt64` elements. -/
structure Config where
  capacity : Nat
  deriving BEq, Repr, Inhabited

def Config.fixedVec (config : Config) : FixedVec :=
  { buffer :=
      { name := "transientVec64"
        capacityBytes := 8 * config.capacity
        alignment := 8
        frameBytes := ProofForge.Svm.Heap.defaultFrameBytes }
    elementBytes := 8
    capacity := config.capacity }

def Config.wellFormed (config : Config) : Bool :=
  config.fixedVec.wellFormed

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
  | .length config => s!"tv64.len.{config.capacity}"
  | .get config =>
      let suffix := String.intercalate "," (operands.map renderValue).toList
      s!"tv64.get.{config.capacity}({suffix})"
  | .pop config => s!"tv64.pop.{config.capacity}"

inductive Call (V : Type) where
  | begin (config : Config)
  | push (config : Config) (value : V)
  | set (config : Config) (index value : V)
  | truncate (config : Config) (newLength : V)
  | clear (config : Config)
  | finish (config : Config)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .begin config => .begin config
  | .push config value => .push config (mapValue value)
  | .set config index value => .set config (mapValue index) (mapValue value)
  | .truncate config newLength => .truncate config (mapValue newLength)
  | .clear config => .clear config
  | .finish config => .finish config

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .begin config => return .begin config
  | .push config value => return .push config (← mapValue value)
  | .set config index value => return .set config (← mapValue index) (← mapValue value)
  | .truncate config newLength => return .truncate config (← mapValue newLength)
  | .clear config => return .clear config
  | .finish config => return .finish config

def Call.values : Call V → Array V
  | .begin _ | .clear _ | .finish _ => #[]
  | .push _ value | .truncate _ value => #[value]
  | .set _ index value => #[index, value]

def Call.effects (_call : Call V) : AccountStorage.EffectSummary := {}

def Call.minAccounts (measure : V → Nat) (call : Call V) : Nat :=
  call.values.foldl (init := 0) fun current value => Nat.max current (measure value)

def Call.wellFormed (valueWellFormed : V → Bool) : Call V → Bool
  | .begin config | .clear config | .finish config => config.wellFormed
  | .push config value | .truncate config value =>
      config.wellFormed && valueWellFormed value
  | .set config index value =>
      config.wellFormed && valueWellFormed index && valueWellFormed value

def Call.canonical (renderValue : V → String) : Call V → String
  | .begin config => s!"tv64.begin.{config.capacity}"
  | .push config value => s!"tv64.push.{config.capacity}({renderValue value})"
  | .set config index value =>
      s!"tv64.set.{config.capacity}({renderValue index},{renderValue value})"
  | .truncate config newLength =>
      s!"tv64.truncate.{config.capacity}({renderValue newLength})"
  | .clear config => s!"tv64.clear.{config.capacity}"
  | .finish config => s!"tv64.finish.{config.capacity}"

end ProofForge.Svm.TransientVec
