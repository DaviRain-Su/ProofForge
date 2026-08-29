import ProofForge.Svm.Component
import ProofForge.Svm.AccountView.Emit
import ProofForge.Svm.AccountStorage.Emit
import ProofForge.Svm.BatchRecorder.Emit
import ProofForge.Svm.FifoCancel.Emit
import ProofForge.Svm.Memory.Emit
import ProofForge.Svm.TransientVec.Emit

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

private def Context.accountView (context : Context) : AccountView.Emit.Context :=
  { loadValue := context.loadValue
    headerStack := context.headerStack
    accountCount := context.accountCount }

private def Context.batchRecorder (context : Context) : BatchRecorder.Emit.Context :=
  { loadValue := context.loadValue
    headerStack := context.headerStack
    accountCount := context.accountCount }

private def Context.fifoCancel (context : Context) : FifoCancel.Emit.Context :=
  { loadValue := context.loadValue
    loadOwnerIsSelf := context.loadOwnerIsSelf
    headerStack := context.headerStack
    accountCount := context.accountCount }

private def Context.memory (context : Context) : Memory.Emit.Context :=
  { loadValue := context.loadValue
    loadOwnerIsSelf := context.loadOwnerIsSelf
    headerStack := context.headerStack }

private def Context.transientVec (context : Context) : TransientVec.Emit.Context :=
  { loadValue := context.loadValue }

/-- Backend implementations needed by component-owned dispatch. The main emitter supplies this
record once and remains independent of individual component call constructors. -/
structure Backend where
  accountStorage : AccountStorage.Emit.MutationBackend

def emitQuery (context : Context) (query : Component.Query) (operands : Array Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String :=
  match query with
  | .accountStorage storageQuery =>
      AccountStorage.Emit.emitQuery context.accountStorage storageQuery operands stackOff nonce scope
  | .accountView viewQuery =>
      AccountView.Emit.emitQuery context.accountView viewQuery operands stackOff nonce scope
  | .fifoCancel cancelQuery =>
      FifoCancel.Emit.emitQuery scope cancelQuery operands stackOff
  | .memory memoryQuery =>
      Memory.Emit.emitQuery context.memory memoryQuery operands stackOff nonce scope
  | .transientVec vectorQuery =>
      TransientVec.Emit.emitQuery context.transientVec vectorQuery operands stackOff nonce scope

def emitCall (context : Context) (backend : Backend) (label : String) :
    Component.Call Ops.Val → Except String String
  | .accountStorage call =>
      AccountStorage.Emit.emitCall context.accountStorage backend.accountStorage label call
  | .batchRecorder call =>
      BatchRecorder.Emit.emitCall context.batchRecorder label call
  | .fifoCancel call =>
      FifoCancel.Emit.emitCall context.fifoCancel backend.accountStorage label call
  | .memory call => Memory.Emit.emitCall context.memory label call
  | .transientVec call => TransientVec.Emit.emitCall context.transientVec label call

end ProofForge.Svm.Component.Emit
