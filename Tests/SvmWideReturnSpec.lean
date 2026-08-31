import Lean
import ProofForge
import ProofForge.Svm.Sdk.TransientRecord64

/-!
Regression coverage for statically shaped wide returns after SVM component effects. The fixture
uses only the existing invocation-local `Record64` facade so it exercises the generic
Extract-to-CFG return boundary independently of any typed wide-vector SDK.
-/

namespace Tests.SvmWideReturnSpec

open Lean Elab Command
open ProofForge
open ProofForge.Core.Value
open ProofForge.Svm
open ProofForge.Svm.Sdk

namespace Fixture

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] private def words : Transient.Record64 := Transient.Record64.bounded 2 1
@[pf_inline] private def widerWords : Transient.Record64 := Transient.Record64.bounded 4 1

@[pf_entry]
def init (initial : UInt64) : State := { dummy := initial }

@[pf_entry]
def get (state : State) : UInt64 := state.dummy

private def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def touch (state : State) : Except Error (State × UInt64) :=
  if state.dummy < u64Max then
    let next := state.dummy + 1
    .ok ({ dummy := next }, next)
  else
    .error .rejected

@[pf_entry]
def readWide (_state : State) (index : UInt64) : UInt128 :=
  let _ := words.begin
  let _ := words.append2 11 12
  let w0 := words.getLimb index 0
  let w1 := words.getLimb index 1
  { w0, w1 }

@[pf_entry]
def readWider (_state : State) (index : UInt64) : UInt256 :=
  let _ := widerWords.begin
  let _ := widerWords.append4 21 22 23 24
  let w0 := widerWords.getLimb index 0
  let w1 := widerWords.getLimb index 1
  let w2 := widerWords.getLimb index 2
  let w3 := widerWords.getLimb index 3
  { w0, w1, w2, w3 }

end Fixture

private def sourceReturns (ops : Array Extract.IR.Op) : Array Extract.IR.Val :=
  ops.filterMap fun
    | .returnU64 value => some value
    | _ => none

private partial def hasSourceReturnState (ops : Array Extract.IR.Op) : Bool :=
  ops.any fun
    | .returnState _ => true
    | .ite _ _ _ yes no => hasSourceReturnState yes || hasSourceReturnState no
    | .forBody _ body => hasSourceReturnState body
    | _ => false

private def cfgReturns (graph : IR.CFG) : Array (Array ProofForge.Svm.Ops.Val) :=
  graph.blocks.filterMap fun block =>
    match block.terminator with
    | .exit (.returnU64 value) => some #[value]
    | .exit (.returnU64s values) => some values
    | _ => none

elab "#pf_guard_svm_wide_returns" : command => do
  let env ← getEnv
  let source ←
    match Extract.extractModuleIR env `Tests.SvmWideReturnSpec.Fixture with
    | .ok source => pure source
    | .error reason => throwError reason
  let some sourceScalar := source.methods.find? (·.ixName == "get")
    | throwError "missing source scalar get"
  let some sourceWide := source.methods.find? (·.ixName == "readWide")
    | throwError "missing source readWide"
  let some sourceWider := source.methods.find? (·.ixName == "readWider")
    | throwError "missing source readWider"
  unless sourceScalar.retCount == 1 &&
      sourceReturns sourceScalar.ops == #[.field (.arg 0) "dummy"] do
    throwError "ordinary scalar return changed while materializing wide results"
  unless sourceWide.retSchema == .scalar .uint128 && sourceWide.retCount == 2 &&
      sourceReturns sourceWide.ops == #[.local 0, .local 1] &&
      !hasSourceReturnState sourceWide.ops do
    throwError "UInt128 component result lost its complete static return frame"
  unless sourceWider.retSchema == .scalar .uint256 && sourceWider.retCount == 4 &&
      sourceReturns sourceWider.ops == #[.local 0, .local 1, .local 2, .local 3] &&
      !hasSourceReturnState sourceWider.ops do
    throwError "UInt256 component result lost its complete static return frame"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some scalar := program.methods.find? (·.ixName == "get")
    | throwError "missing projected scalar get"
  let some wide := program.methods.find? (·.ixName == "readWide")
    | throwError "missing projected readWide"
  let some wider := program.methods.find? (·.ixName == "readWider")
    | throwError "missing projected readWider"
  let toGraph (method : IR.Method) : CommandElabM IR.CFG :=
    match method.toCFG with
    | .ok graph => pure graph
    | .error reason => throwError reason
  let truncated := { wide with ops := wide.ops.pop }
  match truncated.toCFG with
  | .error reason =>
      unless reason.contains "returns 1 of 2 result leaves" do
        throwError s!"wrong truncated result-frame rejection: {reason}"
  | .ok _ => throwError "SVM CFG accepted a truncated result frame"
  let implicitState := {
    wide with ops := wide.ops.pop.pop |>.push (.returnState (.local 0))
  }
  match implicitState.toCFG with
  | .error reason =>
      unless reason.contains "lost its explicit result frame" do
        throwError s!"wrong implicit result-frame rejection: {reason}"
  | .ok _ => throwError "SVM CFG inferred a wide result from nearby locals"
  unless cfgReturns (← toGraph scalar) == #[#[.field (.arg 0) "dummy"]] &&
      cfgReturns (← toGraph wide) == #[#[.local 0, .local 1]] &&
      cfgReturns (← toGraph wider) == #[#[.local 0, .local 1, .local 2, .local 3]] do
    throwError "generic CFG lowering truncated a static scalar result frame"
  let asm ←
    match Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "lddw r2, 8\n  call sol_set_return_data" &&
      asm.contains "lddw r2, 16\n  call sol_set_return_data" &&
      asm.contains "lddw r2, 32\n  call sol_set_return_data" do
    throwError "SVM return-data emission did not preserve scalar/UInt128/UInt256 byte widths"

#pf_guard_svm_wide_returns

end Tests.SvmWideReturnSpec
