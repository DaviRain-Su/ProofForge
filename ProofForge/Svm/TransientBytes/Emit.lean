import ProofForge.Svm.Heap.Emit
import ProofForge.Svm.Ops
import ProofForge.Svm.TransientBytes

namespace ProofForge.Svm.TransientBytes.Emit

structure Context where
  loadValue : Ops.Val → Nat → Nat → String → Except String String

private def failure (code : Nat) : String :=
  s!"  lddw r0, 0x{Core.IR.u64Hex (UInt64.ofNat code)}\n  exit\n"

private def activeMagic : Nat := 0x5046425954333401

private def emitRequireActive (config : Config) (label : String) : String :=
  let active := s!"transient_bytes_active_{label}"
  let capacity := s!"transient_bytes_capacity_{label}"
  s!"\
  ldxdw r1, [r10 - {TransientBytes.activeStack}]
  lddw r2, {activeMagic}
  jeq r1, r2, {active}
{failure stateErrorCode}{active}:
  ldxdw r1, [r10 - {TransientBytes.capacityStack}]
  lddw r2, {config.capacity}
  jeq r1, r2, {capacity}
{failure stateErrorCode}{capacity}:
"

private def emitBegin (label : String) (config : Config) : Except String String := do
  let allocate ← Heap.Emit.emitAllocate "transient_bytes" label
    config.fixedVec.buffer.capacityBytes config.fixedVec.buffer.alignment pointerStack
    (failure oomErrorCode)
  return allocate ++ s!"\
  lddw r1, 0
  stxdw [r10 - {lengthStack}], r1
  lddw r1, {config.capacity}
  stxdw [r10 - {capacityStack}], r1
  lddw r1, {activeMagic}
  stxdw [r10 - {activeStack}], r1
"

private def emitPush (context : Context) (label : String) (config : Config)
    (byte : Ops.Val) : Except String String := do
  let load ← context.loadValue byte 8 0 s!"{label}_byte"
  let inRange := s!"transient_bytes_push_range_{label}"
  let room := s!"transient_bytes_push_room_{label}"
  return load ++ emitRequireActive config label ++ s!"\
  ldxdw r2, [r10 - 8]
  mov64 r3, 255
  jle r2, r3, {inRange}
{failure rangeErrorCode}{inRange}:\
  ldxdw r2, [r10 - {lengthStack}]
  lddw r3, {config.capacity}
  jlt r2, r3, {room}
{failure boundsErrorCode}{room}:
  ldxdw r9, [r10 - {pointerStack}]
  add64 r9, r2
  ldxdw r1, [r10 - 8]
  stxb [r9 + 0], r1
  ldxdw r2, [r10 - {lengthStack}]
  add64 r2, 1
  stxdw [r10 - {lengthStack}], r2
"

private def emitAppendLe64 (context : Context) (label : String) (config : Config)
    (value : Ops.Val) : Except String String := do
  let load ← context.loadValue value 8 0 s!"{label}_value"
  let room := s!"transient_bytes_append_room_{label}"
  let stages := Id.run do
    let mut text := ""
    for k in [0:8] do
      text := text ++ s!"\n  stxb [r9 + {k}], r1"
      unless k == 7 do
        text := text ++ "\n  rsh64 r1, 8"
    return "  ldxdw r1, [r10 - 8]\n" ++ text ++ "\n"
  return load ++ emitRequireActive config label ++ s!"\
  ldxdw r2, [r10 - {lengthStack}]
  add64 r2, 8
  lddw r3, {config.capacity}
  jle r2, r3, {room}
{failure boundsErrorCode}{room}:
  ldxdw r9, [r10 - {pointerStack}]
  ldxdw r2, [r10 - {lengthStack}]
  add64 r9, r2
" ++ stages ++ s!"\
  ldxdw r2, [r10 - {lengthStack}]
  add64 r2, 8
  stxdw [r10 - {lengthStack}], r2
"

private def emitSet (context : Context) (label : String) (config : Config)
    (index byte : Ops.Val) : Except String String := do
  let loadIndex ← context.loadValue index 8 0 s!"{label}_index"
  let loadByte ← context.loadValue byte 16 1 s!"{label}_byte"
  let inRange := s!"transient_bytes_set_range_{label}"
  let inBounds := s!"transient_bytes_set_bounds_{label}"
  return loadIndex ++ loadByte ++ emitRequireActive config label ++ s!"\
  ldxdw r2, [r10 - 16]
  mov64 r3, 255
  jle r2, r3, {inRange}
{failure rangeErrorCode}{inRange}:\
  ldxdw r2, [r10 - 8]
  ldxdw r3, [r10 - {lengthStack}]
  jlt r2, r3, {inBounds}
{failure boundsErrorCode}{inBounds}:
  ldxdw r9, [r10 - {pointerStack}]
  add64 r9, r2
  ldxdw r1, [r10 - 16]
  stxb [r9 + 0], r1
"

private def emitClear (label : String) (config : Config) : String :=
  emitRequireActive config label ++ s!"\
  lddw r1, 0
  stxdw [r10 - {lengthStack}], r1
"

private def emitFinish (label : String) (config : Config) : String :=
  emitRequireActive config label ++ s!"\
  lddw r1, 0
  stxdw [r10 - {pointerStack}], r1
  stxdw [r10 - {lengthStack}], r1
  stxdw [r10 - {capacityStack}], r1
  stxdw [r10 - {activeStack}], r1
"

def emitQuery (context : Context) (query : Query) (operands : Array Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String :=
  match query, operands with
  | .length config, #[] =>
      return emitRequireActive config s!"{scope}_{nonce}_length" ++ s!"\
  ldxdw r1, [r10 - {lengthStack}]
  stxdw [r10 - {stackOff}], r1
"
  | .get config, #[index] => do
      let loadIndex ← context.loadValue index (stackOff + 8) (nonce + 1) s!"{scope}_index"
      let label := s!"{scope}_{nonce}_{stackOff}_get"
      let inBounds := s!"transient_bytes_get_bounds_{label}"
      return loadIndex ++ emitRequireActive config label ++ s!"\
  ldxdw r2, [r10 - {stackOff + 8}]
  ldxdw r3, [r10 - {lengthStack}]
  jlt r2, r3, {inBounds}
{failure boundsErrorCode}{inBounds}:
  ldxdw r9, [r10 - {pointerStack}]
  add64 r9, r2
  ldxb r1, [r9 + 0]
  stxdw [r10 - {stackOff}], r1
"
  | _, _ => throw "extract/ir: malformed transient-byte query operands"

def emitCall (context : Context) (label : String) :
    Call Ops.Val → Except String String
  | .begin config => emitBegin label config
  | .push config byte => emitPush context label config byte
  | .appendLe64 config value => emitAppendLe64 context label config value
  | .set config index byte => emitSet context label config index byte
  | .clear config => return emitClear label config
  | .finish config => return emitFinish label config

end ProofForge.Svm.TransientBytes.Emit