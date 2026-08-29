import ProofForge.Svm.Memory
import ProofForge.Svm.Ops

namespace ProofForge.Svm.Memory.Emit

structure Context where
  loadValue : Ops.Val → Nat → Nat → String → Except String String
  loadOwnerIsSelf : Nat → Nat → String → String
  headerStack : Nat → Nat

private def failure : String :=
  "  lddw r0, 0x1\n  exit\n"

/-- Validate one fixed span against the invocation's actual account data length, then leave its
transient pointer in `r{pointerRegister}`. The pointer exists only across the immediately following
host call and is never represented in source or IR values. -/
private def emitSpanPointer (context : Context) (span : Span) (pointerRegister : Nat)
    (label : String) : String :=
  let ok := s!"memory_span_ok_{label}_{pointerRegister}"
  let loadBase :=
    if span.account == 0 then
      s!"  mov64 r{pointerRegister}, r6\n  add64 r{pointerRegister}, ACC0_DATA\n"
    else
      s!"  ldxdw r{pointerRegister}, [r10 - {context.headerStack span.account}]\n" ++
        s!"  add64 r{pointerRegister}, 88\n"
  let loadLength :=
    if span.account == 0 then "  ldxdw r4, [r6 + ACC0_DATA_LEN]\n"
    else s!"  ldxdw r4, [r10 - {context.headerStack span.account}]\n  ldxdw r4, [r4 + 80]\n"
  s!"\
  ; checked account span acc={span.account} offset={span.offsetBytes} length={span.lengthBytes}
{loadLength}  lddw r5, {span.endOffset}
  jge r4, r5, {ok}
{failure}{ok}:
{loadBase}  add64 r{pointerRegister}, {span.offsetBytes}
"

private def emitDestinationAccess (context : Context) (destination : Span)
    (label : String) : String :=
  let owner := context.loadOwnerIsSelf destination.account 8 s!"{label}_owner"
  let writable := s!"memory_writable_{label}"
  let owned := s!"memory_owned_{label}"
  s!"\
  ldxdw r8, [r10 - {context.headerStack destination.account}]
  ldxb r1, [r8 + 2]
  jne r1, 0, {writable}
{failure}{writable}:
{owner}  ldxdw r1, [r10 - 8]
  jeq r1, 0, {owned}
{failure}{owned}:
"

private def emitCopy (context : Context) (label syscall : String)
    (destination source : Span) : String :=
  emitDestinationAccess context destination label ++
    emitSpanPointer context destination 1 s!"{label}_dst" ++
    emitSpanPointer context source 2 s!"{label}_src" ++ s!"\
  lddw r3, {destination.lengthBytes}
  call {syscall}
"

def emitQuery (context : Context) (query : Query) (operands : Array Ops.Val)
    (stackOff _nonce : Nat) (scope : String) : Except String String :=
  match query, operands with
  | .compare left right, #[] =>
      .ok <| emitSpanPointer context left 1 s!"{scope}_left" ++
        emitSpanPointer context right 2 s!"{scope}_right" ++ s!"\
  lddw r3, {left.lengthBytes}
  mov64 r4, r10
  add64 r4, -{stackOff}
  call sol_memcmp_
  ldxw r1, [r10 - {stackOff}]
  stxdw [r10 - {stackOff}], r1
"
  | _, _ => .error "extract/ir: malformed SVM memory query"

def emitCall (context : Context) (label : String) :
    Call Ops.Val → Except String String
  | .copyNonoverlapping destination source =>
      .ok (emitCopy context label "sol_memcpy_" destination source)
  | .move destination source =>
      .ok (emitCopy context label "sol_memmove_" destination source)
  | .set destination byte => do
      let loadByte ← context.loadValue byte 16 0 s!"{label}_byte"
      return loadByte ++ emitDestinationAccess context destination label ++
        emitSpanPointer context destination 1 s!"{label}_dst" ++ s!"\
  ldxdw r2, [r10 - 16]
  and64 r2, 0xff
  lddw r3, {destination.lengthBytes}
  call sol_memset_
"

end ProofForge.Svm.Memory.Emit
