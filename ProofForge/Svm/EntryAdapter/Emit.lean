import ProofForge.Svm.IR

namespace ProofForge.Svm.EntryAdapter.Emit

structure Route where
  label : String
  tag : Nat
  minDataLen : Nat
  /-- `none` accepts every length at or above `minDataLen` (used only by the authenticated
  self-entry sink). Raw methods always supply a finite maximum; equal bounds are exact. -/
  maxDataLen : Option Nat
  deriving BEq, Repr, Inhabited

/-- The generic adapter owns packed dispatch and raw preflight; the main emitter only supplies its
existing account-walk, signer-check, and scalar-local layout callbacks. -/
structure Context where
  headerStack : Nat → Nat
  scalarLocalStackOff : Nat → Option Nat
  walkAccounts : Nat → String → String → String
  signerChecks : Array IR.Op → String → String

private def emitSkipAccount (scope : String) : String :=
  s!"\
  mov64 r5, r8
  add64 r5, 88
  add64 r5, r4
  add64 r5, MAX_PERMITTED_DATA_INCREASE
  mov64 r1, r4
  and64 r1, 7
  jeq r1, 0, raw_walk_al_{scope}
  lddw r3, 8
  sub64 r3, r1
  add64 r5, r3
raw_walk_al_{scope}:
  ldxdw r1, [r5 + 0]
  add64 r5, 8
  mov64 r8, r5
"

/-- Locate instruction data after the runtime account count without retaining dynamic account
pointers. A selected handler subsequently walks its own statically declared prefix. -/
private def locateInstructionData (scope err : String) : String :=
  s!"\
  ldxdw r2, [r6 + NUM_ACCOUNTS]
  jgt r2, 64, {err}
  mov64 r8, r6
  add64 r8, 8
  lddw r9, 0
raw_walk_loop_{scope}:
  jeq r9, r2, raw_walk_done_{scope}
  ldxb r1, [r8 + 0]
  jne r1, 0xff, {err}
  ldxdw r4, [r8 + 80]
{emitSkipAccount scope}  add64 r9, 1
  ja raw_walk_loop_{scope}
raw_walk_done_{scope}:
"

def emitRoute (routes : Array Route) (fallback err : String) : String := Id.run do
  let mut out := locateInstructionData "route" err
  let mut matchedRoutes := ""
  for i in [0:routes.size] do
    let route := routes[i]!
    let next := s!"raw_route_next_{i}"
    let matched := s!"raw_route_match_{i}"
    let lengthCheck :=
      match route.maxDataLen with
      | some maxDataLen =>
          if route.minDataLen == maxDataLen then
            s!"  jne r2, {route.minDataLen}, {next}\n"
          else
            s!"  jlt r2, {route.minDataLen}, {next}\n  jgt r2, {maxDataLen}, {next}\n"
      | none => s!"  jlt r2, {route.minDataLen}, {next}\n"
    out := out ++ s!"\
  ldxdw r2, [r8 + 0]
{lengthCheck}\
  ldxb r1, [r8 + 8]
  jeq r1, {route.tag}, {matched}
{next}:
"
    -- Conditional jumps only have a signed 16-bit offset. Keep them local and use a 32-bit
    -- call for handlers that can be far away in a large generated program.
    matchedRoutes := matchedRoutes ++ s!"{matched}:\n  call {route.label}\n  exit\n"
  out ++ s!"  ja {fallback}\n" ++ matchedRoutes

private def loadInsn : Nat → Except String String
  | 1 => pure "ldxb"
  | 2 => pure "ldxh"
  | 4 => pure "ldxw"
  | 8 => pure "ldxdw"
  | width => throw s!"extract/unsupported: raw parameter width {width}"

private def emitProgramAccountCheck (context : Context) (entry : RawEntry)
    (err : String) : String :=
  let header := context.headerStack entry.programAccount
  s!"\
  ; authenticate the declared executable program account against the current program id
  ldxdw r3, [r10 - {header}]
  ldxb r1, [r3 + 3]
  jeq r1, 0, {err}
  add64 r3, 8
  mov64 r2, r8
  ldxdw r4, [r8 + 0]
  add64 r2, 8
  add64 r2, r4
  ldxdw r1, [r3 + 0]
  ldxdw r4, [r2 + 0]
  jne r1, r4, {err}
  ldxdw r1, [r3 + 8]
  ldxdw r4, [r2 + 8]
  jne r1, r4, {err}
  ldxdw r1, [r3 + 16]
  ldxdw r4, [r2 + 16]
  jne r1, r4, {err}
  ldxdw r1, [r3 + 24]
  ldxdw r4, [r2 + 24]
  jne r1, r4, {err}
"

private def emitPackedArgs (context : Context) (method : IR.Method)
    (entry : RawEntry) : Except String String := do
  let base := method.rawArgLocalBase
  let mut offset := 1
  let mut out := ""
  for i in [0:entry.paramWidths.size] do
    let width := entry.paramWidths[i]!
    let load ← loadInsn width
    let some localOff := context.scalarLocalStackOff (base + i)
      | throw "extract/unsupported: raw entry exceeds scalar local scratch"
    out := out ++ s!"\
  {load} r1, [r8 + {8 + offset}]
  stxdw [r10 - {localOff}], r1
"
    offset := offset + width
  return out

private def emitBorshArgs (context : Context) (method : IR.Method)
    (entry : RawEntry) (err : String) : Except String String := do
  let base := method.rawArgLocalBase
  let prefixCount := entry.fixedParamCount
  let mut prefixBytes := 0
  let mut out := ""
  for i in [0:prefixCount] do
    let width := entry.paramWidths[i]!
    let load ← loadInsn width
    let some localOff := context.scalarLocalStackOff (base + i)
      | throw "extract/unsupported: raw entry exceeds scalar local scratch"
    out := out ++ s!"\
  {load} r1, [r8 + {9 + prefixBytes}]
  stxdw [r10 - {localOff}], r1
"
    prefixBytes := prefixBytes + width
  out := out ++ s!"\
  ; decode a bounded Borsh Option suffix with exact cursor consumption
  mov64 r7, r8
  add64 r7, {9 + prefixBytes}
  mov64 r9, r8
  ldxdw r1, [r8 + 0]
  add64 r9, 8
  add64 r9, r1
"
  for i in [0:entry.optionWidths.size] do
    let width := entry.optionWidths[i]!
    let load ← loadInsn width
    let presenceIndex := base + prefixCount + 2 * i
    let valueIndex := presenceIndex + 1
    let some presenceOff := context.scalarLocalStackOff presenceIndex
      | throw "extract/unsupported: raw entry exceeds scalar local scratch"
    let some valueOff := context.scalarLocalStackOff valueIndex
      | throw "extract/unsupported: raw entry exceeds scalar local scratch"
    let noneLabel := s!"raw_borsh_none_{method.ixName}_{i}"
    let doneLabel := s!"raw_borsh_done_{method.ixName}_{i}"
    out := out ++ s!"\
  jge r7, r9, {err}
  ldxb r1, [r7 + 0]
  add64 r7, 1
  jeq r1, 0, {noneLabel}
  jne r1, 1, {err}
  mov64 r2, r7
  add64 r2, {width}
  jgt r2, r9, {err}
  lddw r1, 1
  stxdw [r10 - {presenceOff}], r1
  {load} r1, [r7 + 0]
  stxdw [r10 - {valueOff}], r1
  mov64 r7, r2
  ja {doneLabel}
{noneLabel}:
  lddw r1, 0
  stxdw [r10 - {presenceOff}], r1
  stxdw [r10 - {valueOff}], r1
{doneLabel}:
"
  return out ++ s!"  jne r7, r9, {err}\n"

def emitHandler (context : Context) (method : IR.Method) (entry : RawEntry) :
    Except String String := do
  let label := if method.ixName.isEmpty then IR.ixNameOfLean (IR.lastName method.name)
    else method.ixName
  let err := s!"err_raw_{label}"
  let packed ←
    if entry.isExact then emitPackedArgs context method entry
    else emitBorshArgs context method entry err
  let lengthCheck :=
    if entry.isExact then s!"  jne r1, {entry.minDataLen}, {err}\n"
    else s!"  jlt r1, {entry.minDataLen}, {err}\n  jgt r1, {entry.maxDataLen}, {err}\n"
  return s!"\
{label}:
  ldxdw r1, [r6 + NUM_ACCOUNTS]
  jlt r1, {entry.accountCount}, {err}
{context.walkAccounts entry.accountCount label err}{locateInstructionData label err}\
  ; Preserve the actual instruction-data pointer for argument loads, current-program lookup,
  ; self-CPI, and remaining outer accounts beyond the statically consumed prefix.
  stxdw [r10 - {context.headerStack entry.accountCount}], r8
  ldxdw r1, [r8 + 0]
{lengthCheck}\
  ldxb r1, [r8 + 8]
  jne r1, {entry.tag}, {err}
{emitProgramAccountCheck context entry err}{packed}{context.signerChecks method.ops err}\
  ja body_{label}
{err}:
  lddw r0, 0x1
  exit
"

end ProofForge.Svm.EntryAdapter.Emit
