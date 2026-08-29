import ProofForge.Wasm.IR

/-!
# WASM target emitter

Renders one WASM program into an XRPL Bedrock (XLS-0101) shaped Rust source in the
scaffold-xrp / `xrpl_wasm_std` dialect:

- state: one `const {field}_KEY` per UInt64 slot, read through `read_u64`
  (`get_data` on the contract pseudo-account) and written through `write_u64`
  (`set_data`);
- entries: `#[unsafe(no_mangle)] pub extern "C" fn {name}({params}: u64) -> i32` status
  ABI; views: `-> u64` (FFI-safe scalar; multi-value returns fail closed in v0);
- checked arithmetic: Rust `checked_*` with `.ok_or(code)?`; error codes are pinned —
  1 for overflow/underflow of `+ - *`, 2 for divide-by-zero of `/ %`;
- wrapping `+ - *` guard arithmetic uses explicit `wrapping_*` so behavior does not
  depend on the cargo debug/release profile.

Honesty pins: the artifact is source-only (zero-tool); `deployable=false`; no bedrock /
rippled / `ContractCreate` / `ContractCall` / AlphaNet / mainnet claim. The `.rs` is
compiled by an ambient `cargo build --target wasm32-unknown-unknown --release` against
`xrpl-wasm-std` (git rev `ffbe88da26df27e59a72b6202883f42f696933cc`), matching the
scaffold-xrp compilation surface.
-/

namespace ProofForge.Wasm.Emit

open ProofForge.Wasm.IR (Program Method)
open ProofForge.Wasm.Ops

private def rustLit (n : UInt64) : String := s!"{n.toNat}u64"

private def cmpSym : Ops.Cmp → String
  | .eq => "==" | .ne => "!=" | .lt => "<"
  | .le => "<=" | .gt => ">" | .ge => ">="

private def ob : String := "{"
private def cb : String := "}"

/-- Renderer state: fresh temp counter, last materialized value, and the state field the
last checked operation writes into (mirrors the EVM emitter's dest/last contract). -/
private structure EState where
  paramCount : Nat
  fresh : Nat := 0
  last : Option String := none
  pendingDest : Option String := none
  deriving Inhabited

private def fieldOf : Ops.Val → Option String
  | .field (.arg _) name => some name
  | _ => none

private def renderVal (st : EState) (v : Ops.Val) : Except String String :=
  match v with
  | .lit n => .ok (rustLit n)
  | .arg i =>
      if i < st.paramCount then .ok s!"pf_p{i}"
      else .error "extract/unsupported: wasm v0 rejects bare state argument"
  | .field (.arg i) name =>
      if i < st.paramCount then
        .error "extract/unsupported: wasm v0 rejects aggregate parameter projections"
      else .ok s!"{name}_cur"
  | .select cmp lhs rhs thn els => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      let t ← renderVal st thn
      let f ← renderVal st els
      return s!"(if {l} {cmpSym cmp} {r} {ob} {t} {cb} else {ob} {f} {cb})"
  | .addU64 lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return s!"({l}).wrapping_add({r})"
  | .subU64 lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return s!"({l}).wrapping_sub({r})"
  | .mulU64 lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return s!"({l}).wrapping_mul({r})"
  | _ => .error "extract/unsupported: wasm v0 value"

private def indent (n : Nat) (s : String) : String :=
  String.ofList (List.replicate n ' ') ++ s


/-- Rust method and pinned error code for one checked operation. -/
private def checkedInfo : Ops.Op → Option (String × Nat)
  | .checkedAddU64 .. => some ("checked_add", 1)
  | .checkedSubU64 .. => some ("checked_sub", 1)
  | .checkedMulU64 .. => some ("checked_mul", 1)
  | .checkedDivU64 .. => some ("checked_div", 2)
  | .checkedModU64 .. => some ("checked_rem", 2)
  | _ => none

private def isExitOp : Ops.Op → Bool
  | .okState _ | .errorOverflow | .errorNamed _ | .returnU64 _ | .returnState _ => true
  | _ => false

private structure Region where
  lines : Array String := #[]
  st : EState
  terminal : Bool := false

/-- Collect one value plus every directly following `returnU64` into a multi-value return
(mirrors the CFG `returnU64s` grouping), returning the remaining tail. -/
private def collectReturnU64s (first : Ops.Val) (rest : List Ops.Op) :
    Array Ops.Val × List Ops.Op :=
  let rec go (acc : Array Ops.Val) (rest : List Ops.Op) : Array Ops.Val × List Ops.Op :=
    match rest with
    | .returnU64 next :: more => go (acc.push next) more
    | _ => (acc, rest)
  go #[first] rest

/-- Render one flat region: ops until the first terminal exit; trailing exits are dead
(the CFG already validated that shape). `defaultSlot` is the fallback destination for
`okState` values that name no field. -/
private partial def emitRegion (view : Bool) (level : Nat) (defaultSlot : String)
    (ops : List Ops.Op) (st : EState) : Except String Region := do
  match ops with
  | [] =>
      if view then
        throw "extract/unsupported: wasm v0 view region must end in a return"
      else
        throw "extract/unsupported: wasm v0 mutating region must end in a state or error exit"
  | op :: tail =>
    match op with
    | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
    | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
        match checkedInfo op with
        | some (method, code) =>
            let l ← renderVal st lhs
            let r ← renderVal st rhs
            let temp := s!"pf_r{st.fresh}"
            let line := indent level s!"let {temp} = ({l}).{method}({r}).ok_or({code}i32)?;"
            let dest' := (fieldOf lhs).orElse (fun _ => st.pendingDest)
            let st' := { st with fresh := st.fresh + 1, last := some temp, pendingDest := dest' }
            let region ← emitRegion view level defaultSlot tail st'
            return { lines := #[line] ++ region.lines, st := region.st, terminal := true }
        | none => throw "extract/unsupported: wasm v0 checked operation"
    | .ite cmp lhs rhs thn els =>
        let l ← renderVal st lhs
        let r ← renderVal st rhs
        let head := indent level s!"if {l} {cmpSym cmp} {r} {ob}"
        let thenRegion ← emitRegion view (level + 4) defaultSlot thn.toList
          { st with last := none, pendingDest := none }
        unless thenRegion.terminal do
          throw "extract/unsupported: wasm v0 ite branch must end in a terminal"
        let elseRegion ← emitRegion view (level + 4) defaultSlot els.toList
          { st with fresh := thenRegion.st.fresh, last := none, pendingDest := none }
        unless elseRegion.terminal do
          throw "extract/unsupported: wasm v0 ite branch must end in a terminal"
        if tail.isEmpty || tail.all isExitOp then
          -- Both branches exit and no continuation follows: the CFG continuation is
          -- unreachable, so the ite itself terminates the region.
          return {
            lines := #[head] ++ thenRegion.lines ++ #[indent level "} else {"] ++
              elseRegion.lines ++ #[indent level "}"]
            st := elseRegion.st
            terminal := true
          }
        let region ← emitRegion view level defaultSlot tail
          { st with fresh := elseRegion.st.fresh, last := none, pendingDest := none }
        return {
          lines := #[head] ++ thenRegion.lines ++ #[indent level "} else {"] ++
            elseRegion.lines ++ #[indent level "}"] ++ region.lines
          st := region.st
          terminal := true
        }
    | .storeField name value =>
        let v ← renderVal st value
        let line := indent level s!"write_u64({name}_KEY, {v})?;"
        let region ← emitRegion view level defaultSlot tail
          { st with last := some v, pendingDest := some name }
        return { lines := #[line] ++ region.lines, st := region.st, terminal := true }
    | .okState value | .returnState value =>
        if view then throw "extract/unsupported: wasm v0 view cannot write state"
        let dest := st.pendingDest <|> fieldOf value |>.getD defaultSlot
        let v ← match st.last with
          | some e => .ok e
          | none => renderVal st value
        unless tail.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        return {
          lines := #[indent level s!"write_u64({dest}_KEY, {v})?;", indent level "Ok(0)"]
          st, terminal := true
        }
    | .errorOverflow =>
        if view then throw "extract/unsupported: wasm v0 view cannot fail"
        unless tail.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        return { lines := #[indent level "Err(1i32)"], st, terminal := true }
    | .returnU64 value =>
        unless view do
          throw "extract/unsupported: wasm v0 mutating region cannot return a value"
        let (values, skipped) := collectReturnU64s value tail
        unless skipped.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        let mut rendered := #[]
        for v in values do
          rendered := rendered.push (← renderVal st v)
        let inner := String.intercalate ", " rendered.toList
        return { lines := #[indent level inner], st, terminal := true }
    | _ => throw "extract/unsupported: wasm v0 op"

/-- State fields read by one method: `.field (.arg i) name` with `i ≥ paramCount`. -/
private partial def touchedFields (paramCount : Nat) (ops : Array Ops.Op) : Array String :=
  let rec walkVal (acc : Array String) : Ops.Val → Array String
    | .field (.arg i) name => if i ≥ paramCount && !acc.contains name then acc.push name else acc
    | .field base _ => walkVal acc base
    | .select _ lhs rhs thn els =>
        walkVal (walkVal (walkVal (walkVal acc lhs) rhs) thn) els
    | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
    | .divU64 lhs rhs | .modU64 lhs rhs => walkVal (walkVal acc lhs) rhs
    | _ => acc
  let rec walkOp (acc : Array String) : Ops.Op → Array String
    | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
    | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs => walkVal (walkVal acc lhs) rhs
    | .ite _ lhs rhs thn els =>
        let acc := walkVal (walkVal acc lhs) rhs
        let acc := (thn.foldl walkOp acc)
        (els.foldl walkOp acc)
    | .storeField _ value | .okState value | .returnState value | .returnU64 value =>
        walkVal acc value
    | _ => acc
  ops.foldl walkOp #[]

private def paramList (count : Nat) : String :=
  String.intercalate ", " ((List.range count).map (fun i => s!"pf_p{i}: u64"))

private def defaultSlotOf (p : Program) : String :=
  (p.slots[0]?).map (·.name) |>.getD "slot0"

private def renderMutatingFn (p : Program) (method : Method) : Except String (Array String) := do
  let st : EState := { paramCount := method.paramCount }
  let region ← emitRegion false 8 (defaultSlotOf p) method.ops.toList st
  unless region.terminal do
    throw s!"extract/unsupported: {method.ixName} does not end in a terminal"
  let loads := touchedFields method.paramCount method.ops
  let mut lines : Array String := #[]
  lines := lines.push s!"/// @xrpl-function {method.ixName}"
  if method.echoDropped then
    lines := lines.push
      "/// v0 ABI: returns i32 status only; the public result value is elided (read via view)."
  lines := lines.push "#[unsafe(no_mangle)]"
  lines := lines.push
    s!"pub extern \"C\" fn {method.ixName}({paramList method.paramCount}) -> i32 {ob}"
  for field in loads do
    lines := lines.push (indent 4 s!"let {field}_cur = read_u64({field}_KEY);")
  lines := lines.push (indent 4 "let result: Result<i32, i32> = (|| {")
  lines := lines ++ region.lines
  lines := lines.push (indent 4 "})();")
  lines := lines.push (indent 4 "match result {")
  lines := lines.push (indent 8 "Ok(code) => code,")
  lines := lines.push (indent 8 "Err(code) => if code < 0 { code } else { -code },")
  lines := lines.push (indent 4 "}")
  lines := lines.push "}"
  return lines

private def renderViewFn (p : Program) (method : Method) : Except String (Array String) := do
  match method.tupleArity with
  | none => throw s!"extract/unsupported: {method.ixName} view lacks a value ABI"
  | some _arity => do
    let st : EState := { paramCount := method.paramCount }
    let region ← emitRegion true 4 (defaultSlotOf p) method.ops.toList st
    unless region.terminal do
      throw s!"extract/unsupported: {method.ixName} does not end in a terminal"
    let loads := touchedFields method.paramCount method.ops
    let mut lines : Array String := #[]
    lines := lines.push s!"/// @xrpl-function {method.ixName}"
    lines := lines.push "#[unsafe(no_mangle)]"
    lines := lines.push
      s!"pub extern \"C\" fn {method.ixName}({paramList method.paramCount}) -> u64 {ob}"
    for field in loads do
      lines := lines.push (indent 4 s!"let {field}_cur = read_u64({field}_KEY);")
    lines := lines ++ region.lines
    lines := lines.push "}"
    return lines

private def readWriteHelpers : Array String := #[
  "fn read_u64(key: &str) -> u64 {",
  "    let contract_call = get_current_contract_call();",
  "    let contract_account = contract_call.get_contract_account().unwrap();",
  "    match get_data::<u64>(&contract_account, key) {",
  "        Some(value) => value,",
  "        None => 0,",
  "    }",
  "}",
  "",
  "fn write_u64(key: &str, value: u64) -> Result<(), i32> {",
  "    let contract_call = get_current_contract_call();",
  "    let contract_account = contract_call.get_contract_account().unwrap();",
  "    set_data::<u64>(&contract_account, key, value)",
  "}"
]

/-- Render one program as a complete Bedrock-dialect Rust source. The digest line pins the
canonical IR identity of the artifact. -/
def emit (p : Program) : Except String String := do
  let mut lines : Array String := #[]
  lines := lines.push "// PROOF-FORGE-WASM-XRPL v0"
  lines := lines.push s!"// digest={ProofForge.Wasm.IR.digestHex p}"
  lines := lines.push
    "// Generated by ProofForge. Target: XRPL Bedrock (XLS-0101) smart-features."
  lines := lines.push
    "// Source-shaped artifact: wrap in a cdylib crate and build with ambient"
  lines := lines.push
    "// `cargo build --target wasm32-unknown-unknown --release` against xrpl-wasm-std"
  lines := lines.push
    "// (git rev ffbe88da26df27e59a72b6202883f42f696933cc)."
  lines := lines.push
    "// Honesty: zero-tool emission; deployable=false; no bedrock / rippled /"
  lines := lines.push
    "// ContractCreate / ContractCall / AlphaNet / mainnet claim."
  lines := lines.push
    "// v0 ABI: views return u64; mutating entries return i32 status"
  lines := lines.push
    "// (error codes: 1 overflow/underflow, 2 divide-by-zero)."
  lines := lines.push "#![cfg_attr(target_arch = \"wasm32\", no_std)]"
  lines := lines.push ""
  lines := lines.push "#[cfg(not(target_arch = \"wasm32\"))]"
  lines := lines.push "extern crate std;"
  lines := lines.push ""
  lines := lines.push "use xrpl_wasm_std::core::current_tx::contract_call::get_current_contract_call;"
  lines := lines.push "use xrpl_wasm_std::core::current_tx::traits::ContractCallFields;"
  lines := lines.push "use xrpl_wasm_std::core::data::codec::{get_data, set_data};"
  lines := lines.push ""
  for slot in p.slots do
    lines := lines.push s!"const {slot.name}_KEY: &str = \"{slot.name}\";"
  unless p.slots.isEmpty do
    lines := lines.push ""
  lines := lines ++ readWriteHelpers
  lines := lines.push ""
  lines := lines ++ (← renderMutatingFn p p.initializer)
  lines := lines.push ""
  for method in p.entries do
    lines := lines ++ (←
      if method.tupleArity.isSome then renderViewFn p method
      else renderMutatingFn p method)
    lines := lines.push ""
  return String.intercalate "\n" lines.toList ++ "\n"

end ProofForge.Wasm.Emit