import ProofForge.Svm.IR

namespace ProofForge.Svm.EntryAdapter.Emit

structure Route where
  label : String
  tag : Nat
  variant : Option Nat := none
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
    let selectorCheck := match route.variant with
      | none => s!"  jeq r1, {route.tag}, {matched}\n"
      | some variant => s!"\
  jne r1, {route.tag}, {next}
  ldxb r1, [r8 + 9]
  jeq r1, {variant}, {matched}
"
    out := out ++ s!"\
  ldxdw r2, [r8 + 0]
{lengthCheck}\
  ldxb r1, [r8 + 8]
{selectorCheck}\
{next}:
"
    -- Conditional jumps only have a signed 16-bit offset. Keep them local and use a 32-bit
    -- call for handlers that can be far away in a large generated program.
    matchedRoutes := matchedRoutes ++ s!"{matched}:\n  call {route.label}\n  exit\n"
  out ++ s!"  ja {fallback}\n" ++ matchedRoutes

private def emitLoadLE (baseReg : String) (offset width : Nat) : Except String String := do
  unless 1 ≤ width && width ≤ 8 do
    throw s!"extract/unsupported: raw parameter width {width}"
  let direct := match width with
    | 1 => some "ldxb"
    | 2 => some "ldxh"
    | 4 => some "ldxw"
    | 8 => some "ldxdw"
    | _ => none
  match direct with
  | some load => return s!"  {load} r1, [{baseReg} + {offset}]\n"
  | none =>
      let mut out := "  lddw r1, 0\n"
      for i in [0:width] do
        out := out ++ s!"  ldxb r2, [{baseReg} + {offset + i}]\n"
        if i > 0 then out := out ++ s!"  lsh64 r2, {8 * i}\n"
        out := out ++ "  or64 r1, r2\n"
      return out

private def emitStoreStackLE (sourceOff destinationOff width : Nat) : Except String String := do
  unless 1 ≤ width && width ≤ 8 do
    throw s!"extract/unsupported: raw return width {width}"
  let direct := match width with
    | 1 => some "stxb"
    | 2 => some "stxh"
    | 4 => some "stxw"
    | 8 => some "stxdw"
    | _ => none
  let mut out := s!"  ldxdw r1, [r10 - {sourceOff}]\n"
  match direct with
  | some store => return out ++ s!"  {store} [r10 - {destinationOff}], r1\n"
  | none =>
      for i in [0:width] do
        out := out ++ s!"  stxb [r10 - {destinationOff - i}], r1\n"
        if i + 1 < width then out := out ++ "  rsh64 r1, 8\n"
      return out

/-- Serialize a compile-time-shaped scalar product without a heap object or protocol operation.
Each source value is already one widened scalar; this codec only chooses its exact little-endian
wire width and calls the standard return-data syscall. A trailing narrow scalar reserves enough
padding for the emitter's full-width temporary store, but that padding is not returned. -/
def emitReturnValues
    (loadValue : Ops.Val → Nat → Nat → String → Except String String)
    (scratchLimit : Nat) (widths : Array Nat) (values : Array Ops.Val)
    (fresh : Nat) (scope : String) : Except String String := do
  if values.isEmpty then throw "svm/cfg: empty return tuple"
  unless widths.size == values.size do
    throw "extract/unsupported: packed return plan does not match result leaves"
  unless widths.all fun width => 1 ≤ width && width ≤ 8 do
    throw "extract/unsupported: packed return leaf widths must be in 1..8"
  let byteCount := widths.foldl (init := 0) (· + ·)
  let scratchBytes := byteCount + (8 - widths.back!)
  if scratchBytes > scratchLimit then
    throw "extract/unsupported: return tuple exceeds scalar scratch"
  let mut body := ""
  let mut consumed := 0
  let mut nonce := fresh
  for i in [0:values.size] do
    let stackOff := scratchBytes - consumed
    body := body ++ (← loadValue values[i]! stackOff nonce s!"{scope}_return_{i}")
    consumed := consumed + widths[i]!
    nonce := nonce + 1
  return body ++ s!"\
  mov64 r1, r10
  add64 r1, -{scratchBytes}
  lddw r2, {byteCount}
  call sol_set_return_data
  lddw r0, 0
  exit
"

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
    (entry : RawEntry) (err : String) : Except String String := do
  let base := method.rawArgLocalBase
  let mut offset := if entry.variant.isSome then 2 else 1
  let mut out := ""
  let widths := entry.wireParamWidths
  for i in [0:widths.size] do
    let width := widths[i]!
    let some localOff := context.scalarLocalStackOff (base + i)
      | throw "extract/unsupported: raw entry exceeds scalar local scratch"
    let boolGuard :=
      if (entry.paramLeafBooleans[i]?).getD false then s!"  jgt r1, 1, {err}\n" else ""
    out := out ++ (← emitLoadLE "r8" (8 + offset) width) ++ boolGuard ++ s!"\
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
    let some localOff := context.scalarLocalStackOff (base + i)
      | throw "extract/unsupported: raw entry exceeds scalar local scratch"
    out := out ++ (← emitLoadLE "r8" (9 + prefixBytes) width) ++ s!"\
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
{← emitLoadLE "r7" 0 width}\
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

private def emitZeroBorshLocals (context : Context) (base : Nat)
    (locals : Array Nat) : Except String String := do
  let mut out := "  lddw r1, 0\n"
  for localIndex in locals do
    let some stackOff := context.scalarLocalStackOff (base + localIndex)
      | throw "extract/unsupported: Borsh plan exceeds scalar local scratch"
    out := out ++ s!"  stxdw [r10 - {stackOff}], r1\n"
  return out

/-- Validate one contiguous Borsh String payload before copying it into fixed scalar locals. The
finite-state scan accepts Unicode scalar UTF-8 and rejects overlong, surrogate, truncated, and
greater-than-U+10FFFF sequences. `r7` remains the payload cursor. -/
private def emitUtf8Guard (lengthOff : Nat) (err scope : String) (fresh : Nat) : String :=
  let loop := s!"borsh_schema_utf8_loop_{scope}_{fresh}"
  let continuation := s!"borsh_schema_utf8_cont_{scope}_{fresh}"
  let start2 := s!"borsh_schema_utf8_start2_{scope}_{fresh}"
  let start3 := s!"borsh_schema_utf8_start3_{scope}_{fresh}"
  let start4 := s!"borsh_schema_utf8_start4_{scope}_{fresh}"
  let start3E0 := s!"borsh_schema_utf8_start3_e0_{scope}_{fresh}"
  let start3Ed := s!"borsh_schema_utf8_start3_ed_{scope}_{fresh}"
  let start4F0 := s!"borsh_schema_utf8_start4_f0_{scope}_{fresh}"
  let start4F4 := s!"borsh_schema_utf8_start4_f4_{scope}_{fresh}"
  let next := s!"borsh_schema_utf8_next_{scope}_{fresh}"
  let done := s!"borsh_schema_utf8_done_{scope}_{fresh}"
  s!"\
  lddw r2, 0
  lddw r3, 0
  lddw r4, 128
  lddw r5, 191
{loop}:
  ldxw r1, [r10 - {lengthOff}]
  jge r2, r1, {done}
  mov64 r1, r7
  add64 r1, r2
  ldxb r0, [r1 + 0]
  jne r3, 0, {continuation}
  jle r0, 127, {next}
  jlt r0, 194, {err}
  jle r0, 223, {start2}
  jle r0, 239, {start3}
  jle r0, 244, {start4}
  ja {err}
{start2}:
  lddw r3, 1
  ja {next}
{start3}:
  lddw r3, 2
  jeq r0, 224, {start3E0}
  jeq r0, 237, {start3Ed}
  ja {next}
{start3E0}:
  lddw r4, 160
  ja {next}
{start3Ed}:
  lddw r5, 159
  ja {next}
{start4}:
  lddw r3, 3
  jeq r0, 240, {start4F0}
  jeq r0, 244, {start4F4}
  ja {next}
{start4F0}:
  lddw r4, 144
  ja {next}
{start4F4}:
  lddw r5, 143
  ja {next}
{continuation}:
  jlt r0, r4, {err}
  jgt r0, r5, {err}
  sub64 r3, 1
  lddw r4, 128
  lddw r5, 191
{next}:
  add64 r2, 1
  ja {loop}
{done}:
  jne r3, 0, {err}
"

/-- Serialize a bounded source frame to canonical Borsh output. The maximum frame is fixed in
stack scratch, while `sol_set_return_data` observes only `u32 length || active elements`. String
reuses the same strict UTF-8 scanner as input decoding before publishing any bytes. -/
def emitBorshReturnValues
    (loadValue : Ops.Val → Nat → Nat → String → Except String String)
    (scratchLimit : Nat) (plan : BorshReturnPlan) (values : Array Ops.Val)
    (fresh : Nat) (scope : String) : Except String String := do
  let widths := plan.elementWidths
  unless !widths.isEmpty && widths.all fun width => 1 ≤ width && width ≤ 8 do
    throw "extract/unsupported: malformed bounded Borsh return element widths"
  unless values.size == plan.sourceValueCount do
    throw "extract/unsupported: bounded Borsh return plan does not match result leaves"
  let elementBytes := widths.foldl (init := 0) (· + ·)
  let scratchBytes := plan.maxBytes
  let stagingOff := scratchBytes + 8
  if stagingOff > scratchLimit then
    throw "extract/unsupported: bounded Borsh return exceeds scalar scratch"
  let invalid := s!"borsh_return_invalid_{scope}_{fresh}"
  let mut body ← loadValue values[0]! stagingOff fresh s!"{scope}_return_length"
  body := body ++ (← emitStoreStackLE stagingOff scratchBytes 4)
  let mut consumed := 4
  let mut nonce := fresh + 1
  for i in [1:values.size] do
    let width := widths[(i - 1) % widths.size]!
    body := body ++ (← loadValue values[i]! stagingOff nonce s!"{scope}_return_{i}")
    body := body ++ (← emitStoreStackLE stagingOff (scratchBytes - consumed) width)
    consumed := consumed + width
    nonce := nonce + 1
  let utf8 :=
    if plan.validateUtf8 then s!"\
  mov64 r7, r10
  add64 r7, -{scratchBytes - 4}
{emitUtf8Guard scratchBytes invalid (scope ++ "_return") nonce}"
    else ""
  return body ++ s!"\
  ldxw r1, [r10 - {scratchBytes}]
  jgt r1, {plan.capacity}, {invalid}
{utf8}\
  mov64 r1, r10
  add64 r1, -{scratchBytes}
  ldxw r2, [r10 - {scratchBytes}]
  mul64 r2, {elementBytes}
  add64 r2, 4
  call sol_set_return_data
  lddw r0, 0
  exit
{invalid}:
  lddw r0, 0x1
  exit
"

private partial def emitBorshDecode (context : Context) (base : Nat) (err scope : String)
    (fresh : Nat) : BorshDecode → Except String (String × Nat)
  | .sequence items => do
      let mut out := ""
      let mut nonce := fresh
      for item in items do
        let (body, next) ← emitBorshDecode context base err scope nonce item
        out := out ++ body
        nonce := next
      return (out, nonce)
  | .scalar localIndex width canonicalBool => do
      let some stackOff := context.scalarLocalStackOff (base + localIndex)
        | throw "extract/unsupported: Borsh plan exceeds scalar local scratch"
      let boolGuard := if canonicalBool then s!"  jgt r1, 1, {err}\n" else ""
      return (s!"\
  mov64 r2, r7
  add64 r2, {width}
  jgt r2, r9, {err}
{← emitLoadLE "r7" 0 width}{boolGuard}\
  stxdw [r10 - {stackOff}], r1
  add64 r7, {width}
", fresh)
  | .option tagLocal payloadLocals payload => do
      let some tagOff := context.scalarLocalStackOff (base + tagLocal)
        | throw "extract/unsupported: Borsh plan exceeds scalar local scratch"
      let noneLabel := s!"borsh_schema_none_{scope}_{fresh}"
      let doneLabel := s!"borsh_schema_option_done_{scope}_{fresh}"
      let (payloadBody, next) ← emitBorshDecode context base err scope (fresh + 1) payload
      return (s!"\
  jge r7, r9, {err}
  ldxb r1, [r7 + 0]
  add64 r7, 1
  jgt r1, 1, {err}
  stxdw [r10 - {tagOff}], r1
  jeq r1, 0, {noneLabel}
{payloadBody}\
  ja {doneLabel}
{noneLabel}:
{← emitZeroBorshLocals context base payloadLocals}{doneLabel}:
", next)
  | .enumeration tagLocal payloadLocals variants => do
      let some tagOff := context.scalarLocalStackOff (base + tagLocal)
        | throw "extract/unsupported: Borsh plan exceeds scalar local scratch"
      let doneLabel := s!"borsh_schema_enum_done_{scope}_{fresh}"
      let mut out := s!"\
  jge r7, r9, {err}
  ldxb r1, [r7 + 0]
  add64 r7, 1
  stxdw [r10 - {tagOff}], r1
{← emitZeroBorshLocals context base payloadLocals}\
  ldxdw r1, [r10 - {tagOff}]
"
      let mut nonce := fresh + 1
      for i in [0:variants.size] do
        let nextLabel := s!"borsh_schema_enum_next_{scope}_{nonce}"
        let (variantBody, next) ← emitBorshDecode context base err scope (nonce + 1) variants[i]!
        out := out ++ s!"\
  jne r1, {i}, {nextLabel}
{variantBody}\
  ja {doneLabel}
{nextLabel}:
"
        nonce := next
      return (out ++ s!"  ja {err}\n{doneLabel}:\n", nonce)
  | .boundedArray lengthLocal elementLocals elements => do
      let some lengthOff := context.scalarLocalStackOff (base + lengthLocal)
        | throw "extract/unsupported: Borsh plan exceeds scalar local scratch"
      let mut out := s!"\
  mov64 r2, r7
  add64 r2, 4
  jgt r2, r9, {err}
  ldxw r1, [r7 + 0]
  jgt r1, {elements.size}, {err}
  stxdw [r10 - {lengthOff}], r1
  add64 r7, 4
{← emitZeroBorshLocals context base elementLocals}"
      let mut nonce := fresh
      for i in [0:elements.size] do
        let skipLabel := s!"borsh_schema_array_skip_{scope}_{nonce}"
        let (elementBody, next) ←
          emitBorshDecode context base err scope (nonce + 1) elements[i]!
        out := out ++ s!"\
  ldxdw r1, [r10 - {lengthOff}]
  jle r1, {i}, {skipLabel}
{elementBody}{skipLabel}:
"
        nonce := next
      return (out, nonce)
  | .boundedBytes lengthLocal byteLocals validateUtf8 => do
      let some lengthOff := context.scalarLocalStackOff (base + lengthLocal)
        | throw "extract/unsupported: Borsh plan exceeds scalar local scratch"
      let utf8 := if validateUtf8 then emitUtf8Guard lengthOff err scope fresh else ""
      let mut out := s!"\
  mov64 r2, r7
  add64 r2, 4
  jgt r2, r9, {err}
  ldxw r1, [r7 + 0]
  jgt r1, {byteLocals.size}, {err}
  stxdw [r10 - {lengthOff}], r1
  add64 r7, 4
  mov64 r2, r7
  add64 r2, r1
  jgt r2, r9, {err}
{← emitZeroBorshLocals context base byteLocals}{utf8}"
      let mut nonce := fresh + if validateUtf8 then 1 else 0
      for i in [0:byteLocals.size] do
        let some byteOff := context.scalarLocalStackOff (base + byteLocals[i]!)
          | throw "extract/unsupported: Borsh plan exceeds scalar local scratch"
        let skipLabel := s!"borsh_schema_bytes_skip_{scope}_{nonce}"
        out := out ++ s!"\
  ldxdw r1, [r10 - {lengthOff}]
  jle r1, {i}, {skipLabel}
  ldxb r1, [r7 + 0]
  stxdw [r10 - {byteOff}], r1
  add64 r7, 1
{skipLabel}:
"
        nonce := nonce + 1
      return (out, nonce)

/-- Interpret target-owned schema plans with one bounded cursor. All logical values land in fixed
scalar locals; absent Option payloads, inactive enum lanes, and unused bounded-array elements are
canonical zero. -/
private def emitSchemaBorshArgs (context : Context) (method : IR.Method)
    (entry : RawEntry) (err : String) : Except String String := do
  let base := method.rawArgLocalBase
  let mut out := s!"\
  ; decode recursive target-owned Borsh schema with exact cursor consumption
  mov64 r7, r8
  add64 r7, {9 + if entry.variant.isSome then 1 else 0}
  mov64 r9, r8
  ldxdw r1, [r8 + 0]
  add64 r9, 8
  add64 r9, r1
"
  let mut nonce := 0
  for i in [0:entry.paramBorshPlans.size] do
    let plan := entry.paramBorshPlans[i]!
    let localBase := base + entry.paramLeafStart i
    let (body, next) ← emitBorshDecode context localBase err method.ixName nonce plan.decode
    out := out ++ body
    nonce := next
  return out ++ s!"  jne r7, r9, {err}\n"

def emitHandler (context : Context) (method : IR.Method) (entry : RawEntry) :
    Except String String := do
  let label := if method.ixName.isEmpty then IR.ixNameOfLean (IR.lastName method.name)
    else method.ixName
  let err := s!"err_raw_{label}"
  let packed ←
    if entry.usesSchemaBorsh then emitSchemaBorshArgs context method entry err
    else if entry.isExact then emitPackedArgs context method entry err
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
{match entry.variant with
  | none => ""
  | some variant => s!"  ldxb r1, [r8 + 9]\n  jne r1, {variant}, {err}\n"}\
{emitProgramAccountCheck context entry err}{packed}{context.signerChecks method.ops err}\
  ja body_{label}
{err}:
  lddw r0, 0x1
  exit
"

end ProofForge.Svm.EntryAdapter.Emit
