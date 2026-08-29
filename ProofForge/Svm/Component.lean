import ProofForge.Svm.AccountStorage
import ProofForge.Svm.AccountView
import ProofForge.Svm.BatchRecorder
import ProofForge.Svm.FifoCancel
import ProofForge.Svm.Memory
import ProofForge.Svm.Telemetry
import ProofForge.Svm.TransientBytes
import ProofForge.Svm.TransientVec

namespace ProofForge.Svm.Component

/-- Highest fixed stack offset owned by current bounded components. Scalar-local planning starts
after this component-wide boundary instead of knowing individual storage/queue/recorder layouts. -/
def stackScratchEnd : Nat := 408

/-- Transitive component effects use one target-owned account summary regardless of component. -/
abbrev EffectSummary := AccountStorage.EffectSummary

/-- Stable value-producing bridge for target-owned bounded components. Generic SVM Ops, IR, CFG,
and the main emitter traverse this wrapper once; component-specific query vocabularies remain in
their owning modules. -/
inductive Query where
  | accountStorage (query : AccountStorage.Query)
  | accountView (query : AccountView.Query)
  | fifoCancel (query : FifoCancel.Query)
  | memory (query : Memory.Query)
  | telemetry (query : Telemetry.Query)
  | transientVec (query : TransientVec.Query)
  | transientBytes (query : TransientBytes.Query)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .accountStorage query => query.arity
  | .accountView query => query.arity
  | .fifoCancel _ => 0
  | .memory query => query.arity
  | .telemetry query => query.arity
  | .transientVec query => query.arity
  | .transientBytes query => query.arity

def Query.effects : Query → EffectSummary
  | .accountStorage query => query.effects
  | .accountView query => query.effects
  | .fifoCancel _ => {}
  | .memory query => query.effects
  | .telemetry query => query.effects
  | .transientVec query => query.effects
  | .transientBytes query => query.effects

def Query.wellFormed (accountLimit : Nat := 64) : Query → Bool
  | .accountStorage query => query.wellFormed accountLimit
  | .accountView query => query.wellFormed accountLimit
  | .fifoCancel _ => true
  | .memory query => query.wellFormed accountLimit
  | .telemetry query => query.wellFormed
  | .transientVec query => query.wellFormed
  | .transientBytes query => query.wellFormed

def Query.needsWalk : Query → Bool
  | .accountStorage query => query.needsWalk
  | .accountView _ => true
  | .fifoCancel _ => false
  | .memory query => query.needsWalk
  | .telemetry query => query.needsWalk
  | .transientVec query => query.needsWalk
  | .transientBytes query => query.needsWalk

def Query.minAccounts (measure : V → Nat) (operands : Array V) : Query → Nat
  | .accountStorage query => query.minAccounts measure operands
  | .accountView query => query.minAccounts measure operands
  | .fifoCancel _ => operands.foldl (init := 0) fun current value =>
      Nat.max current (measure value)
  | .memory query => query.minAccounts measure operands
  | .telemetry query => query.minAccounts measure operands
  | .transientVec query => query.minAccounts measure operands
  | .transientBytes query => query.minAccounts measure operands

def Query.canonical (renderValue : V → String) (operands : Array V) : Query → String
  | .accountStorage query => query.canonical renderValue operands
  | .accountView query => query.canonical renderValue operands
  | .fifoCancel query =>
      if operands.isEmpty then query.canonical
      else s!"invalid-{query.canonical}-{operands.size}"
  | .memory query => query.canonical renderValue operands
  | .telemetry query => query.canonical renderValue operands
  | .transientVec query => query.canonical renderValue operands
  | .transientBytes query => query.canonical renderValue operands

/-- Stable effect bridge for target-owned bounded components. New queue, map, allocator, recorder,
or codec components extend this layer instead of adding top-level SVM Ops/IR/main-emitter cases. -/
inductive Call (V : Type) where
  | accountStorage (call : AccountStorage.Call V)
  | batchRecorder (call : BatchRecorder.Call V)
  | fifoCancel (call : FifoCancel.Call V)
  | memory (call : Memory.Call V)
  | telemetry (call : Telemetry.Call V)
  | transientVec (call : TransientVec.Call V)
  | transientBytes (call : TransientBytes.Call V)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .accountStorage call => .accountStorage (call.mapValues mapValue)
  | .batchRecorder call => .batchRecorder (call.mapValues mapValue)
  | .fifoCancel call => .fifoCancel (call.mapValues mapValue)
  | .memory call => .memory (call.mapValues mapValue)
  | .telemetry call => .telemetry (call.mapValues mapValue)
  | .transientVec call => .transientVec (call.mapValues mapValue)
  | .transientBytes call => .transientBytes (call.mapValues mapValue)

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .accountStorage call => return .accountStorage (← call.mapValuesM mapValue)
  | .batchRecorder call => return .batchRecorder (← call.mapValuesM mapValue)
  | .fifoCancel call => return .fifoCancel (← call.mapValuesM mapValue)
  | .memory call => return .memory (← call.mapValuesM mapValue)
  | .telemetry call => return .telemetry (← call.mapValuesM mapValue)
  | .transientVec call => return .transientVec (← call.mapValuesM mapValue)
  | .transientBytes call => return .transientBytes (← call.mapValuesM mapValue)

def Call.values : Call V → Array V
  | .accountStorage call => call.values
  | .batchRecorder call => call.values
  | .fifoCancel call => call.values
  | .memory call => call.values
  | .telemetry call => call.values
  | .transientVec call => call.values
  | .transientBytes call => call.values

def Call.anyValue (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.any predicate

def Call.allValues (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.all predicate

def Call.effects : Call V → EffectSummary
  | .accountStorage call => call.effects
  | .batchRecorder call => call.effects
  | .fifoCancel call => call.effects
  | .memory call => call.effects
  | .telemetry call => call.effects
  | .transientVec call => call.effects
  | .transientBytes call => call.effects

def Call.minAccounts (measure : V → Nat) : Call V → Nat
  | .accountStorage call => call.minAccounts measure
  | .batchRecorder call => call.minAccounts measure
  | .fifoCancel call => call.minAccounts measure
  | .memory call => call.minAccounts measure
  | .telemetry call => call.minAccounts measure
  | .transientVec call => call.minAccounts measure
  | .transientBytes call => call.minAccounts measure

def Call.wellFormed (valueWellFormed : V → Bool) (accountLimit : Nat := 64) : Call V → Bool
  | .accountStorage call => call.wellFormed valueWellFormed accountLimit
  | .batchRecorder call => call.wellFormed valueWellFormed accountLimit
  | .fifoCancel call => call.wellFormed valueWellFormed accountLimit
  | .memory call => call.wellFormed valueWellFormed accountLimit
  | .telemetry call => call.wellFormed valueWellFormed
  | .transientVec call => call.wellFormed valueWellFormed
  | .transientBytes call => call.wellFormed valueWellFormed

def Call.canonical (renderValue : V → String) : Call V → String
  | .accountStorage call => call.canonical renderValue
  | .batchRecorder call => call.canonical renderValue
  | .fifoCancel call => call.canonical renderValue
  | .memory call => call.canonical renderValue
  | .telemetry call => call.canonical renderValue
  | .transientVec call => call.canonical renderValue
  | .transientBytes call => call.canonical renderValue

def Call.usesCpi : Call V → Bool
  | .accountStorage _ => false
  | .batchRecorder call => call.usesCpi
  | .fifoCancel call => call.usesCpi
  | .memory _ => false
  | .telemetry _ => false
  | .transientVec _ => false
  | .transientBytes _ => false

def Call.stackScratchEnd : Call V → Nat
  | .accountStorage _ => Component.stackScratchEnd
  | .batchRecorder call => call.stackScratchEnd
  | .fifoCancel call => call.stackScratchEnd
  | .memory _ => Component.stackScratchEnd
  | .telemetry _ => Component.stackScratchEnd
  | .transientVec _ => Component.stackScratchEnd
  | .transientBytes _ => Component.stackScratchEnd

def Call.rawSelfEntries : Call V → Array (Nat × String)
  | .accountStorage _ => #[]
  | .batchRecorder call => call.rawSelfEntries
  | .fifoCancel call => call.rawSelfEntries
  | .memory _ => #[]
  | .telemetry _ => #[]
  | .transientVec _ => #[]
  | .transientBytes _ => #[]

end ProofForge.Svm.Component
