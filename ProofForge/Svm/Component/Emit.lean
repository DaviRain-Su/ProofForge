import ProofForge.Svm.Component
import ProofForge.Svm.AccountData.Emit
import ProofForge.Svm.AccountView.Emit
import ProofForge.Svm.AccountStorage.Emit
import ProofForge.Svm.BatchRecorder.Emit
import ProofForge.Svm.FifoCancel.Emit
import ProofForge.Svm.Lamports.Emit
import ProofForge.Svm.Memory.Emit
import ProofForge.Svm.Sysvar.Emit
import ProofForge.Svm.Telemetry.Emit
import ProofForge.Svm.TransientBytes.Emit
import ProofForge.Svm.TransientVec.Emit

namespace ProofForge.Svm.Component.Emit

/-- Generic component emission context. Component backends share value loading and the bounded
walked-account frame; `accountCount` lets invocation-local sinks address the current program without
asking the main emitter for another component-specific callback. -/
structure Context where
  loadValue : Ops.Val → Nat → Nat → String → Except String String
  loadOwnerIsSelf : Nat → Nat → String → String
  headerStack : Nat → Nat
  originalDataLenStack : Nat → Nat
  accountCount : Nat

private def Context.accountStorage (context : Context) : AccountStorage.Emit.Context :=
  { loadValue := context.loadValue
    loadOwnerIsSelf := context.loadOwnerIsSelf
    headerStack := context.headerStack }

private def Context.accountData (context : Context) : AccountData.Emit.Context :=
  { loadValue := context.loadValue
    loadOwnerIsSelf := context.loadOwnerIsSelf
    headerStack := context.headerStack
    originalDataLenStack := context.originalDataLenStack }

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

private def Context.lamports (context : Context) : Lamports.Emit.Context :=
  { loadValue := context.loadValue
    loadOwnerIsSelf := context.loadOwnerIsSelf
    headerStack := context.headerStack }

private def Context.memory (context : Context) : Memory.Emit.Context :=
  { loadValue := context.loadValue
    loadOwnerIsSelf := context.loadOwnerIsSelf
    headerStack := context.headerStack }

private def Context.telemetry (context : Context) : Telemetry.Emit.Context :=
  { loadValue := context.loadValue }

private def Context.transientVec (context : Context) : TransientVec.Emit.Context :=
  { loadValue := context.loadValue }

private def Context.transientBytes (context : Context) : TransientBytes.Emit.Context :=
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
  | .sysvar sysvarQuery =>
      Sysvar.Emit.emitQuery sysvarQuery operands stackOff scope
  | .telemetry telemetryQuery =>
      Telemetry.Emit.emitQuery telemetryQuery operands stackOff
  | .transientVec vectorQuery =>
      TransientVec.Emit.emitQuery context.transientVec vectorQuery operands stackOff nonce scope
  | .transientBytes bytesQuery =>
      TransientBytes.Emit.emitQuery context.transientBytes bytesQuery operands stackOff nonce scope

def emitCall (context : Context) (backend : Backend) (label : String) :
    Component.Call Ops.Val → Except String String
  | .accountData call => AccountData.Emit.emitCall context.accountData label call
  | .accountStorage call =>
      AccountStorage.Emit.emitCall context.accountStorage backend.accountStorage label call
  | .batchRecorder call =>
      BatchRecorder.Emit.emitCall context.batchRecorder label call
  | .fifoCancel call =>
      FifoCancel.Emit.emitCall context.fifoCancel backend.accountStorage label call
  | .lamports call => Lamports.Emit.emitCall context.lamports label call
  | .memory call => Memory.Emit.emitCall context.memory label call
  | .telemetry call => Telemetry.Emit.emitCall context.telemetry label call
  | .transientVec call => TransientVec.Emit.emitCall context.transientVec label call
  | .transientBytes call => TransientBytes.Emit.emitCall context.transientBytes label call

end ProofForge.Svm.Component.Emit
