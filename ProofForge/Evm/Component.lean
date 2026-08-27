import ProofForge.Evm.HashedMap
import ProofForge.Evm.WideWord
import ProofForge.Evm.ClosedCall

namespace ProofForge.Evm.Component

/-- Transitive storage/log/call effects for a bounded EVM component. -/
structure EffectSummary where
  readsStorage : Bool := false
  writesStorage : Bool := false
  logs : Bool := false
  externalCall : Bool := false
  deriving BEq, Repr, Inhabited

def EffectSummary.merge (left right : EffectSummary) : EffectSummary :=
  { readsStorage := left.readsStorage || right.readsStorage
    writesStorage := left.writesStorage || right.writesStorage
    logs := left.logs || right.logs
    externalCall := left.externalCall || right.externalCall }

private def ofHashedMap (effects : HashedMap.EffectSummary) : EffectSummary :=
  { readsStorage := effects.readsStorage
    writesStorage := effects.writesStorage }

private def ofClosedCall (effects : ClosedCall.EffectSummary) : EffectSummary :=
  { readsStorage := effects.readsStorage
    writesStorage := effects.writesStorage
    logs := effects.logs
    externalCall := effects.externalCall }

/-- Stable value-producing bridge. Generic EVM Ops, IR, CFG, and the main emitter traverse this
wrapper once; component-specific query vocabularies remain in their owning modules.

`empty` is a reserved zero-arity placeholder so the sum is inhabited. Source programs must not
emit it. -/
inductive Query where
  | empty
  | hashedMap (query : HashedMap.Query)
  | wideWord (query : WideWord.Query)
  | closedCall (query : ClosedCall.Query)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .empty => 0
  | .hashedMap query => query.arity
  | .wideWord query => query.arity
  | .closedCall query => query.arity

def Query.effects : Query → EffectSummary
  | .empty => {}
  | .hashedMap query => ofHashedMap query.effects
  | .wideWord _ => {}
  | .closedCall query => ofClosedCall query.effects

def Query.wellFormed : Query → Bool
  | .empty => false
  | .hashedMap query => query.wellFormed
  | .wideWord query => query.wellFormed
  | .closedCall query => query.wellFormed

def Query.canonical (renderValue : V → String) (operands : Array V) : Query → String
  | .empty =>
      if operands.isEmpty then "evm.comp.empty"
      else s!"invalid-evm.comp.empty-{operands.size}"
  | .hashedMap query => query.canonical renderValue operands
  | .wideWord query => query.canonical renderValue operands
  | .closedCall query => query.canonical renderValue operands

/-- Stable effect bridge. New hashed-map, LOG, or closed-CALL backends extend this layer instead
of adding top-level EVM Ops/IR/main-emitter cases.

`empty` is reserved and not well-formed. -/
inductive Call (V : Type) where
  | empty
  | hashedMap (call : HashedMap.Call V)
  | closedCall (call : ClosedCall.Call V)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .empty => .empty
  | .hashedMap call => .hashedMap (call.mapValues mapValue)
  | .closedCall call => .closedCall (call.mapValues mapValue)

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .empty => pure .empty
  | .hashedMap call => return .hashedMap (← call.mapValuesM mapValue)
  | .closedCall call => return .closedCall (← call.mapValuesM mapValue)

def Call.values : Call V → Array V
  | .empty => #[]
  | .hashedMap call => call.values
  | .closedCall call => call.values

def Call.anyValue (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.any predicate

def Call.allValues (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.all predicate

def Call.effects : Call V → EffectSummary
  | .empty => {}
  | .hashedMap call => ofHashedMap call.effects
  | .closedCall call => ofClosedCall call.effects

def Call.wellFormed (valueWellFormed : V → Bool) : Call V → Bool
  | .empty => false
  | .hashedMap call => call.wellFormed valueWellFormed
  | .closedCall call => call.wellFormed valueWellFormed

def Call.canonical (renderValue : V → String) : Call V → String
  | .empty => "evm.comp.empty"
  | .hashedMap call => call.canonical renderValue
  | .closedCall call => call.canonical renderValue

def Call.emitsExpired : Call V → Bool
  | .closedCall call => call.emitsExpired
  | _ => false

def Call.emitsUnauthorized : Call V → Bool
  | .closedCall call => call.emitsUnauthorized
  | _ => false

end ProofForge.Evm.Component
