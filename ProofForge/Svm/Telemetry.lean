import ProofForge.Svm.AccountStorage

/-!
# SVM invocation telemetry

Target-owned component vocabulary for Solana's resource and stack introspection syscalls plus the
two allocation-free numeric logging calls. These operations carry no account effects, allocation,
pointer, or persistent state. Generic SVM Ops/IR/CFG use only the existing Component bridge.
-/

namespace ProofForge.Svm.Telemetry

inductive Query where
  | remainingComputeUnits
  | stackHeight
  deriving BEq, Repr, Inhabited

def Query.arity (_query : Query) : Nat := 0

def Query.effects (_query : Query) : AccountStorage.EffectSummary := {}

def Query.wellFormed (_query : Query) : Bool := true

def Query.needsWalk (_query : Query) : Bool := false

def Query.minAccounts (measure : V → Nat) (operands : Array V) (_query : Query) : Nat :=
  operands.foldl (init := 0) fun current value => Nat.max current (measure value)

def Query.canonical (renderValue : V → String) (operands : Array V) : Query → String
  | .remainingComputeUnits =>
      if operands.isEmpty then "telemetry.remainingComputeUnits"
      else s!"invalid-telemetry.remainingComputeUnits-{operands.size}-" ++
        String.intercalate "," (operands.map renderValue).toList
  | .stackHeight =>
      if operands.isEmpty then "telemetry.stackHeight"
      else s!"invalid-telemetry.stackHeight-{operands.size}-" ++
        String.intercalate "," (operands.map renderValue).toList

inductive Call (V : Type) where
  | logComputeUnits
  | log64 (first second third fourth fifth : V)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .logComputeUnits => .logComputeUnits
  | .log64 first second third fourth fifth =>
      .log64 (mapValue first) (mapValue second) (mapValue third) (mapValue fourth)
        (mapValue fifth)

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .logComputeUnits => return .logComputeUnits
  | .log64 first second third fourth fifth =>
      return .log64 (← mapValue first) (← mapValue second) (← mapValue third)
        (← mapValue fourth) (← mapValue fifth)

def Call.values : Call V → Array V
  | .logComputeUnits => #[]
  | .log64 first second third fourth fifth => #[first, second, third, fourth, fifth]

def Call.effects (_call : Call V) : AccountStorage.EffectSummary := {}

def Call.minAccounts (measure : V → Nat) (call : Call V) : Nat :=
  call.values.foldl (init := 0) fun current value => Nat.max current (measure value)

def Call.wellFormed (valueWellFormed : V → Bool) (call : Call V) : Bool :=
  call.values.all valueWellFormed

def Call.canonical (renderValue : V → String) : Call V → String
  | .logComputeUnits => "telemetry.logComputeUnits"
  | .log64 first second third fourth fifth =>
      s!"telemetry.log64({renderValue first},{renderValue second},{renderValue third}," ++
        s!"{renderValue fourth},{renderValue fifth})"

end ProofForge.Svm.Telemetry
