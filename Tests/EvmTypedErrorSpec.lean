import ProofForge
import Examples.EvmTypedErrors

/-!
Parameterized source-error qualification: Core retains one typed fixed frame, EVM derives its
selector/revert/ABI declaration, SVM deliberately erases payloads to its existing named program
error, and unsupported payload shapes fail closed rather than becoming selector-only errors.
-/

namespace Tests.EvmTypedErrorSpec

open Lean Elab Command

private def sampleFrame : ProofForge.Core.Ops.ErrorFrame ProofForge.Evm.Ops.Val := {
  constructor := "denied"
  args := #[{ name := "code", type := .uint64, parts := #[.lit 9] }]
}

#guard sampleFrame.wellFormed (·.wellFormed ProofForge.Evm.Ops.ValKind.arity)
#guard sampleFrame.values == #[.lit 9]
#guard (sampleFrame.mapValues fun _ => (.lit 11 : ProofForge.Evm.Ops.Val)).values == #[.lit 11]
#guard !(ProofForge.Core.Ops.ErrorFrame.wellFormed
  (·.wellFormed ProofForge.Evm.Ops.ValKind.arity)
  ({ sampleFrame with constructor := "" } :
    ProofForge.Core.Ops.ErrorFrame ProofForge.Evm.Ops.Val))
#guard !(ProofForge.Core.Ops.ErrorFrame.wellFormed
  (·.wellFormed ProofForge.Evm.Ops.ValKind.arity)
  ({ sampleFrame with args := sampleFrame.args.push sampleFrame.args[0]! } :
    ProofForge.Core.Ops.ErrorFrame ProofForge.Evm.Ops.Val))

open Examples.EvmTypedErrors in
#guard match update (init 3) 5 1 with
  | .error (.denied code) => code == 1
  | _ => false

open Examples.EvmTypedErrors in
#guard match update (init 3) 3 7 with
  | .error (.conflict expected actual) => expected == 3 && actual == 3
  | _ => false

open Examples.EvmTypedErrors in
#guard match update (init 3) 5 8 with
  | .error (.exhausted current requested authorization limit) =>
      current == 3 && requested == 5 && authorization == 8 && limit == 7
  | _ => false

open Examples.EvmTypedErrors in
#guard match update (init 3) 0 7 with
  | .error .locked => true
  | _ => false

open Examples.EvmTypedErrors in
#guard match update (init 3) 5 7 with
  | .ok (state, result) => state.value == 5 && result == 5
  | _ => false

private partial def sourceFrames (ops : Array ProofForge.Extract.IR.Op) :
    Array (ProofForge.Core.Ops.ErrorFrame ProofForge.Extract.IR.Val) :=
  ops.foldl (init := #[]) fun frames op =>
    let frames := match op with
      | .errorTyped frame => frames.push frame
      | _ => frames
    match op with
    | .ite _ _ _ yes no => frames ++ sourceFrames yes ++ sourceFrames no
    | .forBody _ body => frames ++ sourceFrames body
    | _ => frames

private partial def evmFrames (ops : Array ProofForge.Evm.IR.Op) :
    Array (ProofForge.Core.Ops.ErrorFrame ProofForge.Evm.Ops.Val) :=
  ops.foldl (init := #[]) fun frames op =>
    let frames := match op with
      | .errorTyped frame => frames.push frame
      | _ => frames
    match op with
    | .ite _ _ _ yes no => frames ++ evmFrames yes ++ evmFrames no
    | .forBody _ body => frames ++ evmFrames body
    | _ => frames

private partial def evmHasComponent (ops : Array ProofForge.Evm.IR.Op) : Bool :=
  ops.any fun op =>
    match op with
    | .component _ => true
    | .ite _ _ _ yes no => evmHasComponent yes || evmHasComponent no
    | .forBody _ body => evmHasComponent body
    | _ => false

private partial def svmErrorNames (ops : Array ProofForge.Svm.IR.Op) : Array String :=
  ops.foldl (init := #[]) fun names op =>
    let names := match op with
      | .errorNamed name => names.push name
      | _ => names
    match op with
    | .ite _ _ _ yes no => names ++ svmErrorNames yes ++ svmErrorNames no
    | .forBody _ body => names ++ svmErrorNames body
    | _ => names

private def frameMatches (frame : ProofForge.Core.Ops.ErrorFrame V)
    (constructor : String) (fields : Array String) : Bool :=
  frame.constructor == constructor && frame.args.map (·.name) == fields &&
    frame.args.all fun arg => arg.type == .uint64 && arg.parts.size == 1

private def cfgTypedConstructors (graph : ProofForge.Evm.IR.CFG) : Array String :=
  graph.blocks.filterMap fun block =>
    match block.terminator with
    | .exit (.errorTyped frame) => some frame.constructor
    | _ => none

private def expectUnsupported (env : Environment) (name : Name) (fragment : String) :
    CommandElabM Unit := do
  match ProofForge.Extract.extractMethod env .get name with
  | .ok _ => throwError s!"{name}: unsupported parameterized error unexpectedly extracted"
  | .error reason =>
      unless reason.contains fragment do
        throwError s!"{name}: wrong fail-closed reason: {reason}"

namespace Unsupported

inductive WideError where
  | wide (value : ProofForge.Core.Value.UInt128)

def wide (value : ProofForge.Core.Value.UInt128) : Except WideError UInt64 :=
  .error (.wide value)

inductive ManyError where
  | many (a b c d e : UInt64)

def many (value : UInt64) : Except ManyError UInt64 :=
  .error (.many value value value value value)

inductive AnonymousError where
  | hidden (_ : UInt64)

def anonymous (value : UInt64) : Except AnonymousError UInt64 :=
  .error (.hidden value)

inductive ImplicitError where
  | hidden {code : UInt64}

def implicitField (value : UInt64) : Except ImplicitError UInt64 :=
  .error (.hidden (code := value))

end Unsupported

elab "#pf_guard_evm_typed_errors" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.EvmTypedErrors with
    | .ok source => pure source
    | .error reason => throwError reason
  let some sourceUpdate := source.methods.find? (·.ixName == "update")
    | throwError "typed-error example lost update"
  let sourceFrames := sourceFrames sourceUpdate.ops
  unless sourceFrames.size == 3 &&
      sourceFrames.any (frameMatches · "denied" #["code"]) &&
      sourceFrames.any (frameMatches · "conflict" #["expected", "actual"]) &&
      sourceFrames.any (frameMatches · "exhausted"
        #["current", "requested", "authorization", "limit"]) do
    throwError s!"source typed-error frames diverged: {repr sourceFrames}"

  let evm ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some update := evm.entries.find? (·.ixName == "update")
    | throwError "EVM typed-error example lost update"
  let frames := evmFrames update.ops
  unless frames.size == 3 && !evmHasComponent update.ops do
    throwError "EVM lowering lost typed frames or introduced a component recipe"
  let cfg ←
    match update.toCFG with
    | .ok graph => pure graph
    | .error reason => throwError reason
  let cfgErrors := cfgTypedConstructors cfg
  unless ["denied", "conflict", "exhausted"].all cfgErrors.contains do
    throwError s!"CFG lost typed error exits: {cfgErrors}"

  let abi ←
    match ProofForge.Evm.Emit.emitAbiChecked evm with
    | .ok abi => pure abi
    | .error reason => throwError reason
  let deniedAbi := "{\"type\":\"error\",\"name\":\"denied\",\"inputs\":[" ++
    "{\"name\":\"code\",\"type\":\"uint64\"}]}"
  let conflictAbi := "{\"type\":\"error\",\"name\":\"conflict\",\"inputs\":[" ++
    "{\"name\":\"expected\",\"type\":\"uint64\"}," ++
    "{\"name\":\"actual\",\"type\":\"uint64\"}]}"
  let exhaustedAbi := "{\"type\":\"error\",\"name\":\"exhausted\",\"inputs\":[" ++
    "{\"name\":\"current\",\"type\":\"uint64\"}," ++
    "{\"name\":\"requested\",\"type\":\"uint64\"}," ++
    "{\"name\":\"authorization\",\"type\":\"uint64\"}," ++
    "{\"name\":\"limit\",\"type\":\"uint64\"}]}"
  unless abi.contains deniedAbi && abi.contains conflictAbi && abi.contains exhaustedAbi &&
      abi.contains "{\"type\":\"error\",\"name\":\"locked\",\"inputs\":[]}" do
    throwError s!"typed-error ABI metadata diverged:\n{abi}"

  let yul ←
    match ProofForge.Evm.Emit.emitYul evm with
    | .ok yul => pure yul
    | .error reason => throwError reason
  let deniedSelector := ProofForge.Evm.Keccak.selector "denied" #["uint64"]
  let conflictSelector := ProofForge.Evm.Keccak.selector "conflict" #["uint64", "uint64"]
  let exhaustedSelector := ProofForge.Evm.Keccak.selector "exhausted"
    #["uint64", "uint64", "uint64", "uint64"]
  unless yul.contains s!"shl(224, 0x{deniedSelector})" && yul.contains "revert(0, 36)" &&
      yul.contains s!"shl(224, 0x{conflictSelector})" && yul.contains "revert(0, 68)" &&
      yul.contains s!"shl(224, 0x{exhaustedSelector})" && yul.contains "revert(0, 132)" &&
      yul.contains "revert(0, 4)" do
    throwError "typed-error Yul omitted selector, ordered ABI words, or exact revert geometry"

  let svm ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let some svmUpdate := svm.methods.find? (·.ixName == "update")
    | throwError "SVM typed-error projection lost update"
  let svmErrors := svmErrorNames svmUpdate.ops
  unless ["denied", "conflict", "exhausted", "locked"].all svmErrors.contains do
    throwError s!"SVM did not deliberately erase typed payloads to named errors: {svmErrors}"

  expectUnsupported env ``Unsupported.wide "only UInt64 fields"
  expectUnsupported env ``Unsupported.many "at most four UInt64 fields"
  expectUnsupported env ``Unsupported.anonymous "extract/unsupported"
  expectUnsupported env ``Unsupported.implicitField "explicitly named"

  logInfo s!"EvmTypedErrors digest: {ProofForge.Evm.IR.digestHex evm}"

#pf_guard_evm_typed_errors

end Tests.EvmTypedErrorSpec
