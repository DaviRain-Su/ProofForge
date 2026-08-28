import ProofForge

namespace Tests.CoreCollectionsSpec

open ProofForge.Core.Value

private def short : BoundedVec UInt64 4 :=
  { length := 2, values := #v[11, 13, 0, 0] }

private def full : BoundedVec UInt64 4 :=
  { length := 4, values := #v[11, 13, 17, 19] }

private def malformed : BoundedVec UInt64 4 :=
  { length := 5, values := #v[11, 13, 17, 19] }

#guard short.wellFormed
#guard full.wellFormed
#guard !malformed.wellFormed
#guard short.capacity == 4
#guard short.size == 2
#guard !short.isEmpty
#guard !short.isFull
#guard full.isFull
#guard malformed.isFull

#guard short.get? 0 == some 11
#guard short.get? 1 == some 13
#guard short.get? 2 == none
#guard short.get? 4 == none
#guard short.getD 2 99 == 99

#guard
  match short.set? 1 29 with
  | some next => next.length == 2 && next.values[0] == 11 && next.values[1] == 29
  | none => false

#guard (short.set? 2 29).isNone

#guard
  match short.push? 23 with
  | some (next, index) =>
      index == 2 && next.length == 3 && next.values[2] == 23 && next.values[3] == 0
  | none => false

#guard (full.push? 23).isNone
#guard (malformed.push? 23).isNone

#guard
  match short.pop? with
  | some (next, value) => value == 13 && next.length == 1 && next.values[1] == 13
  | none => false

#guard (({ length := 0, values := #v[0, 0, 0, 0] } : BoundedVec UInt64 4).pop?).isNone
#guard short.clear.length == 0
#guard short.clear.values == short.values

/-! The same helper must remain an extractable source combinator. This probe deliberately carries
the bounded vector through each target's existing input adapter; no collection operation is added
to Core Ops or either target extension. -/
namespace CompileProbe

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

@[pf_entry]
def touch (state : State) : Except Error (State × UInt64) :=
  if state.dummy = 0 then .ok (state, 0) else .error .rejected

@[pf_entry, pf_svm_raw 21 2 0]
def readOr (_state : State) (items : BoundedVec UInt64 4) (index fallback : UInt64) : UInt64 :=
  items.getD index fallback

/-- Multi-limb dynamic elements remain an explicit fail-closed edge in the extraction pipeline. -/
def readWideW0 (_state : State) (items : BoundedVec UInt128 4) (index : UInt64)
    (fallback : UInt128) : UInt64 :=
  (items.getD index fallback).w0

end CompileProbe

open Lean Elab Command

elab "#pf_guard_bounded_vec_cross_target" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Tests.CoreCollectionsSpec.CompileProbe with
    | .ok source => pure source
    | .error reason => throwError reason
  let some readOr := source.methods.find? (·.ixName == "readOr")
    | throwError "missing bounded-vector compile probe"
  unless readOr.paramSchemas == #[.boundedArray 4 (.scalar .uint64), .scalar .uint64,
      .scalar .uint64] do
    throwError s!"bounded-vector helper lost its logical input schema: {repr readOr.paramSchemas}"
  match ProofForge.Extract.extractMethod env .get ``CompileProbe.readWideW0 with
  | .error reason =>
      unless reason.contains "extract/unsupported: body" do
        throwError s!"wrong multi-limb bounded-vector rejection: {reason}"
  | .ok _ => throwError "multi-limb bounded-vector dynamic read did not fail closed"
  let svm ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let evmSource :=
    { source with methods := source.methods.map fun method =>
        { method with annotations := #[] } }
  let evm ←
    match ProofForge.Evm.IR.fromExtracted evmSource with
    | .ok program => pure program
    | .error reason => throwError reason
  let _ ←
    match ProofForge.Svm.Emit.emitAsm svm with
    | .ok asm => pure asm
    | .error reason => throwError reason
  let _ ←
    match ProofForge.Evm.Emit.emitYul evm with
    | .ok yul => pure yul
    | .error reason => throwError reason

#pf_guard_bounded_vec_cross_target

end Tests.CoreCollectionsSpec
