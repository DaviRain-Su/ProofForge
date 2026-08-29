import ProofForge.Svm.Ops
import ProofForge.Svm.Transient.Emit
import ProofForge.Svm.TransientVec

namespace ProofForge.Svm.TransientVec.Emit

structure Context where
  loadValue : Ops.Val → Nat → Nat → String → Except String String

private def activeMagic : Nat := 0x5046564543363401

private def lifecycle : Transient.Emit.Lifecycle :=
  { kind := "transient_vec"
    pointerStack
    lengthStack
    capacityStack
    activeStack
    activeMagic
    oomErrorCode
    stateErrorCode }

/-- The source handle's own metadata bank: slot 0 keeps the historical cells, slot 1 sits one
`slotStride` above. -/
private def pointerCell (config : Config) : Nat :=
  Transient.Emit.slotCell pointerStack config.slot

private def lengthCell (config : Config) : Nat :=
  Transient.Emit.slotCell lengthStack config.slot

private abbrev failure := Transient.Emit.failure

private def emitRequireActive (config : Config) (label : String) : String :=
  Transient.Emit.emitRequireActive lifecycle config.slot config.payload label

private def emitBegin (label : String) (config : Config) : Except String String := do
  Transient.Emit.emitBegin lifecycle config.fixedVec config.slot label

private def emitPush (context : Context) (label : String) (config : Config)
    (value : Ops.Val) : Except String String := do
  let load ← context.loadValue value 8 0 s!"{label}_value"
  let room := s!"transient_vec_push_room_{label}"
  return load ++ emitRequireActive config label ++ s!"\
  ldxdw r2, [r10 - {lengthCell config}]
  lddw r3, {config.payload}
  jlt r2, r3, {room}
{failure boundsErrorCode}{room}:
  ldxdw r9, [r10 - {pointerCell config}]
  mov64 r3, r2
  lsh64 r3, 3
  add64 r9, r3
  ldxdw r1, [r10 - 8]
  stxdw [r9 + 0], r1
  add64 r2, 1
  stxdw [r10 - {lengthCell config}], r2
"

private def emitSet (context : Context) (label : String) (config : Config)
    (index value : Ops.Val) : Except String String := do
  let loadIndex ← context.loadValue index 8 0 s!"{label}_index"
  let loadValue ← context.loadValue value 16 1 s!"{label}_value"
  let inBounds := s!"transient_vec_set_bounds_{label}"
  return loadIndex ++ loadValue ++ emitRequireActive config label ++ s!"\
  ldxdw r2, [r10 - 8]
  ldxdw r3, [r10 - {lengthCell config}]
  jlt r2, r3, {inBounds}
{failure boundsErrorCode}{inBounds}:
  ldxdw r9, [r10 - {pointerCell config}]
  lsh64 r2, 3
  add64 r9, r2
  ldxdw r1, [r10 - 16]
  stxdw [r9 + 0], r1
"

private def emitTruncate (context : Context) (label : String) (config : Config)
    (newLength : Ops.Val) : Except String String := do
  let load ← context.loadValue newLength 8 0 s!"{label}_new_length"
  return load ++ Transient.Emit.emitTruncate lifecycle config.payload 8 config.slot label

private def emitClear (label : String) (config : Config) : String :=
  Transient.Emit.emitClear lifecycle config.payload config.slot label

private def emitFinish (label : String) (config : Config) : String :=
  Transient.Emit.emitFinish lifecycle config.payload config.slot label

def emitQuery (context : Context) (query : Query) (operands : Array Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String :=
  match query, operands with
  | .length config, #[] =>
      return emitRequireActive config s!"{scope}_{nonce}_length" ++ s!"\
  ldxdw r1, [r10 - {lengthCell config}]
  stxdw [r10 - {stackOff}], r1
"
  | .get config, #[index] => do
      let loadIndex ← context.loadValue index (stackOff + 8) (nonce + 1) s!"{scope}_index"
      let label := s!"{scope}_{nonce}_{stackOff}_get"
      let inBounds := s!"transient_vec_get_bounds_{label}"
      return loadIndex ++ emitRequireActive config label ++ s!"\
  ldxdw r2, [r10 - {stackOff + 8}]
  ldxdw r3, [r10 - {lengthCell config}]
  jlt r2, r3, {inBounds}
{failure boundsErrorCode}{inBounds}:
  ldxdw r9, [r10 - {pointerCell config}]
  lsh64 r2, 3
  add64 r9, r2
  ldxdw r1, [r9 + 0]
  stxdw [r10 - {stackOff}], r1
"
  | .pop config, #[] =>
      let label := s!"{scope}_{nonce}_{stackOff}_pop"
      let nonEmpty := s!"transient_vec_pop_nonempty_{label}"
      return emitRequireActive config label ++ s!"\
  ldxdw r2, [r10 - {lengthCell config}]
  jgt r2, 0, {nonEmpty}
{failure boundsErrorCode}{nonEmpty}:
  sub64 r2, 1
  stxdw [r10 - {lengthCell config}], r2
  ldxdw r9, [r10 - {pointerCell config}]
  mov64 r3, r2
  lsh64 r3, 3
  add64 r9, r3
  ldxdw r1, [r9 + 0]
  stxdw [r10 - {stackOff}], r1
"
  | _, _ => throw "extract/ir: malformed transient-vector query operands"

def emitCall (context : Context) (label : String) :
    Call Ops.Val → Except String String
  | .begin config => emitBegin label config
  | .push config value => emitPush context label config value
  | .set config index value => emitSet context label config index value
  | .truncate config newLength => emitTruncate context label config newLength
  | .clear config => return emitClear label config
  | .finish config => return emitFinish label config

end ProofForge.Svm.TransientVec.Emit
