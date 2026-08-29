import ProofForge.Svm.Ops
import ProofForge.Svm.Sysvar

namespace ProofForge.Svm.Sysvar.Emit

/-- Deep scratch for the largest supported sysvar representation. It remains disjoint from
expression temporaries, scalar locals, walked-account headers, and CPI scratch. -/
private def scratch : Nat := 3072

private def emitClockField (field : String) (offset stackOff : Nat) (scope : String) : String :=
  s!"\
  ; load clock.{field} via sol_get_clock_sysvar
  mov64 r1, r10
  add64 r1, -{scratch}
  call sol_get_clock_sysvar
  jeq r0, 0, clock_{field}_ok_{scope}_{stackOff}
  lddw r0, 0x1
  exit
clock_{field}_ok_{scope}_{stackOff}:
  ldxdw r1, [r10 - {scratch - offset}]
  stxdw [r10 - {stackOff}], r1
"

private def emitEpochScheduleField
    (field : String) (offset stackOff : Nat) (scope : String) : String :=
  s!"\
  ; load {field} via sol_get_epoch_schedule_sysvar
  mov64 r1, r10
  add64 r1, -{scratch}
  call sol_get_epoch_schedule_sysvar
  jeq r0, 0, epoch_ok_{scope}_{stackOff}
  lddw r0, 0x1
  exit
epoch_ok_{scope}_{stackOff}:
  ldxdw r1, [r10 - {scratch - offset}]
  stxdw [r10 - {stackOff}], r1
"

private def emitRentExemption (dataLen stackOff : Nat) (scope : String) : String :=
  s!"\
  ; load rentExemption {dataLen} via sol_get_rent_sysvar
  mov64 r1, r10
  add64 r1, -{scratch}
  call sol_get_rent_sysvar
  jeq r0, 0, rent_ok_{scope}_{stackOff}
  lddw r0, 0x1
  exit
rent_ok_{scope}_{stackOff}:
  ldxdw r1, [r10 - {scratch}]
  lddw r2, {128 + dataLen}
  mul64 r1, r2
  stxdw [r10 - {stackOff}], r1
"

def emitQuery (query : Query) (operands : Array Ops.Val) (stackOff : Nat)
    (scope : String) : Except String String :=
  match query, operands with
  | .clock .slot, #[] => .ok (emitClockField "slot" 0 stackOff scope)
  | .clock .epoch, #[] => .ok (emitClockField "epoch" 16 stackOff scope)
  | .clock .unixTimestamp, #[] => .ok (emitClockField "unix" 32 stackOff scope)
  | .epochSchedule .slotsPerEpoch, #[] =>
      .ok (emitEpochScheduleField "slotsPerEpoch" 0 stackOff scope)
  | .rentExemption dataLen, #[] => .ok (emitRentExemption dataLen.toNat stackOff scope)
  | _, _ => .error "extract/ir: malformed SVM sysvar query operands"

end ProofForge.Svm.Sysvar.Emit
