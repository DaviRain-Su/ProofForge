import ProofForge.Svm.Component
import ProofForge.Svm.AccountStorage.Emit

namespace ProofForge.Svm.Component.Emit

/-- Generic component emission context. Component backends share value loading and the bounded
walked-account frame; `accountCount` lets invocation-local sinks address the current program without
asking the main emitter for another component-specific callback. -/
structure Context where
  loadValue : Ops.Val → Nat → Nat → String → Except String String
  loadOwnerIsSelf : Nat → Nat → String → String
  headerStack : Nat → Nat
  accountCount : Nat

private def Context.accountStorage (context : Context) : AccountStorage.Emit.Context :=
  { loadValue := context.loadValue
    loadOwnerIsSelf := context.loadOwnerIsSelf
    headerStack := context.headerStack }

/-- Backend implementations needed by component-owned dispatch. The main emitter supplies this
record once and remains independent of individual component call constructors. -/
structure Backend where
  accountStorage : AccountStorage.Emit.MutationBackend

def emitQuery (context : Context) (query : Component.Query) (operands : Array Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String :=
  match query with
  | .accountStorage storageQuery =>
      AccountStorage.Emit.emitQuery context.accountStorage storageQuery operands stackOff nonce scope

def emitCall (context : Context) (backend : Backend) (label : String) :
    Component.Call Ops.Val → Except String String
  | .accountStorage call =>
      AccountStorage.Emit.emitCall context.accountStorage backend.accountStorage label call

end ProofForge.Svm.Component.Emit
