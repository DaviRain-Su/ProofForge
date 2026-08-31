import Lean

open Lean

namespace ProofForge.Attr

/-- Source declaration for a target-owned packed Solana entry adapter. `accountCount` is the
number of protocol accounts consumed by the method, and `programAccount` is the physical account
whose key must equal the currently executing program id. -/
structure SvmRawEntry where
  tag : Nat
  accountCount : Nat
  programAccount : Nat
  /-- Optional Borsh enum discriminant immediately after the instruction tag. Multiple handlers
  may share a tag when each owns a distinct variant. The validated discriminant is not passed as
  a method parameter. -/
  variant : Option Nat := none
  /-- A fixed-width prefix followed by Borsh `Option<T>` fields. Each option lowers to two method
  parameters: a u8 presence flag and a scalar payload of the declared width. Empty means the
  original exact fixed-width adapter. -/
  prefixParamCount : Nat := 0
  optionWidths : Array Nat := #[]
  /-- Exact little-endian widths for a statically shaped return product. Empty retains the normal
  consecutive-u64 return ABI. This is wire metadata, not an executable operation. -/
  returnWidths : Array Nat := #[]
  /-- The first result leaf is a 0/1 presence flag and is not serialized. Zero completes without
  setting return data; one serializes the remaining leaves with `returnWidths`. -/
  optionalReturnData : Bool := false
  deriving BEq, Repr, Inhabited

syntax (name := pf_svm_raw)
  "pf_svm_raw" num num num : attr

syntax (name := pf_svm_raw_borsh_options)
  "pf_svm_raw_borsh_options" num num num num "[" num,* "]" : attr

syntax (name := pf_svm_raw_return)
  "pf_svm_raw_return" num num num "[" num,* "]" : attr

syntax (name := pf_svm_raw_variant_return)
  "pf_svm_raw_variant_return" num num num num "[" num,* "]" : attr

syntax (name := pf_svm_raw_variant_optional_return)
  "pf_svm_raw_variant_optional_return" num num num num "[" num,* "]" : attr

/-- Declare the exact prior NEAR state-schema digest accepted by one migration entry. -/
syntax (name := pf_near_migrate)
  "pf_near_migrate" num : attr

private partial def syntaxNatLiterals (node : Syntax) : Array Nat :=
  match node.isNatLit? with
  | some value => #[value]
  | none => node.getArgs.flatMap syntaxNatLiterals

/-- 只标记可编译根。种类由返回类型推断。 -/
initialize pfEntryAttr : TagAttribute ←
  registerTagAttribute `pf_entry
    "mark a Lean definition as a ProofForge compile root"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_entry is not a definition"

/-- 显式允许抽出器在控制流边界 β 展开的已检查、有界 helper。 -/
initialize pfInlineAttr : TagAttribute ←
  registerTagAttribute `pf_inline
    "allow the ProofForge extractor to inline a bounded helper definition"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_inline is not a definition"

/-- Mark a compiler-owned structure or inductive as an ordinary logical contract-boundary
value. This is intentionally representation-free: the shared codec still derives and validates
its complete field/variant schema, while each target owns its wire layout. The marker exists so
reusable SDK value types under the reserved `ProofForge` namespace do not need one-off extractor
or emitter cases. -/
initialize pfBoundaryAttr : TagAttribute ←
  registerTagAttribute `pf_boundary
    "allow a compiler-owned datatype to use the generic ProofForge boundary codec"
    fun decl => do
      unless decl.toString.startsWith "ProofForge." do
        throwError "extract/unsupported: pf_boundary is reserved for compiler-owned ProofForge datatypes"
      let env ← getEnv
      match env.find? decl with
      | some (.inductInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_boundary is not a structure or inductive"

/-- Mark one NEAR entry as callable only when predecessor and current AccountId are equal. -/
initialize pfNearPrivateAttr : TagAttribute ←
  registerTagAttribute `pf_near_private
    "declare a NEAR private entry wrapper"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_near_private is not a definition"

/-- Mark one mutating NEAR entry or initializer as accepting an attached deposit. -/
initialize pfNearPayableAttr : TagAttribute ←
  registerTagAttribute `pf_near_payable
    "declare a NEAR payable entry wrapper"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_near_payable is not a definition"

/-- Mark one explicit logical-Unit NEAR mutator as matching near-sdk's omitted-return wrapper:
persist state but do not call `value_return`. Without this marker explicit Unit remains JSON null. -/
initialize pfNearVoidAttr : TagAttribute ←
  registerTagAttribute `pf_near_void
    "declare a NEAR mutator with an empty success return"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_near_void is not a definition"

/-- Mark an exact mutating U128 result as a dual terminal: immediate quoted JSON when no returned
Promise was staged on the branch, otherwise `promise_return` of that one Promise. -/
initialize pfNearPromiseOrValueAttr : TagAttribute ←
  registerTagAttribute `pf_near_promise_or_value
    "declare a NEAR mutator returning either quoted U128 or one Promise"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_near_promise_or_value is not a definition"

/-- Mark one NEAR mutator as an explicit migration from one exact prior schema digest. Target
binding additionally requires an explicit private attribute and rejects payable migration. -/
initialize pfNearMigrateAttr : ParametricAttribute Nat ←
  registerParametricAttribute {
    name := `pf_near_migrate
    descr := "declare an authenticated NEAR migration from one exact state-schema digest"
    getParam := fun decl stx => do
      let values := syntaxNatLiterals stx
      unless values.size == 1 do
        throwError "invalid pf_near_migrate syntax"
      let digest := values[0]!
      unless digest ≤ 18446744073709551615 do
        throwError "extract/unsupported: pf_near_migrate digest must fit UInt64"
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure digest
      | _ => throwError "extract/unsupported: pf_near_migrate is not a definition"
  }

/--
Attach one packed-u8 Solana wire entry to a `@[pf_entry]` method without introducing an executable
Op. Parameter widths come from the Lean method type; dispatch, account walking, and program-account
authentication belong to the target-owned entry-adapter backend.
-/
initialize pfSvmRawAttr : ParametricAttribute SvmRawEntry ←
  registerParametricAttribute {
    name := `pf_svm_raw
    descr := "declare a packed-u8 Solana raw entry adapter"
    getParam := fun decl stx => do
      let values := syntaxNatLiterals stx
      unless values.size == 3 do
        throwError "invalid pf_svm_raw syntax"
      let entry : SvmRawEntry := {
        tag := values[0]!
        accountCount := values[1]!
        programAccount := values[2]!
      }
      unless entry.tag < 256 do
        throwError "extract/unsupported: pf_svm_raw tag must fit u8"
      unless 0 < entry.accountCount && entry.accountCount ≤ 64 do
        throwError "extract/unsupported: pf_svm_raw accounts must be in 1..64"
      unless entry.programAccount < entry.accountCount do
        throwError "extract/unsupported: pf_svm_raw program account is out of range"
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure entry
      | _ => throwError "extract/unsupported: pf_svm_raw is not a definition"
  }

/--
Attach a variable-length Borsh adapter whose method parameters are a fixed scalar prefix followed
by `(presence : UInt8, value)` pairs. The option widths are restricted to the same scalar widths as
the fixed adapter. The target adapter validates every discriminant, every conditional payload, and
exact cursor consumption; no codec operation enters source Ops or generic IR.
-/
initialize pfSvmRawBorshOptionsAttr : ParametricAttribute SvmRawEntry ←
  registerParametricAttribute {
    name := `pf_svm_raw_borsh_options
    descr := "declare a packed-u8 Solana raw entry with a Borsh Option suffix"
    getParam := fun decl stx => do
      let values := syntaxNatLiterals stx
      unless values.size ≥ 5 do
        throwError "invalid pf_svm_raw_borsh_options syntax"
      let entry : SvmRawEntry := {
        tag := values[0]!
        accountCount := values[1]!
        programAccount := values[2]!
        prefixParamCount := values[3]!
        optionWidths := values.extract 4 values.size
      }
      unless entry.tag < 256 do
        throwError "extract/unsupported: pf_svm_raw_borsh_options tag must fit u8"
      unless 0 < entry.accountCount && entry.accountCount ≤ 64 do
        throwError "extract/unsupported: pf_svm_raw_borsh_options accounts must be in 1..64"
      unless entry.programAccount < entry.accountCount do
        throwError "extract/unsupported: pf_svm_raw_borsh_options program account is out of range"
      unless entry.optionWidths.all fun width =>
          width == 1 || width == 2 || width == 4 || width == 8 do
        throwError "extract/unsupported: Borsh option payloads must be u8/u16/u32/u64"
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure entry
      | _ => throwError "extract/unsupported: pf_svm_raw_borsh_options is not a definition"
  }

/--
Attach an exact packed-input raw entry with an exact fixed-width scalar return product. The return
codec is owned by the SVM EntryAdapter and therefore does not add a source Op, generic CFG exit, or
protocol-specific emitter branch.
-/
initialize pfSvmRawReturnAttr : ParametricAttribute SvmRawEntry ←
  registerParametricAttribute {
    name := `pf_svm_raw_return
    descr := "declare a packed-u8 Solana raw entry with a fixed-width return product"
    getParam := fun decl stx => do
      let values := syntaxNatLiterals stx
      unless values.size ≥ 4 do
        throwError "invalid pf_svm_raw_return syntax"
      let entry : SvmRawEntry := {
        tag := values[0]!
        accountCount := values[1]!
        programAccount := values[2]!
        returnWidths := values.extract 3 values.size
      }
      unless entry.tag < 256 do
        throwError "extract/unsupported: pf_svm_raw_return tag must fit u8"
      unless 0 < entry.accountCount && entry.accountCount ≤ 64 do
        throwError "extract/unsupported: pf_svm_raw_return accounts must be in 1..64"
      unless entry.programAccount < entry.accountCount do
        throwError "extract/unsupported: pf_svm_raw_return program account is out of range"
      unless entry.returnWidths.all fun width =>
          width == 1 || width == 2 || width == 4 || width == 8 do
        throwError "extract/unsupported: packed returns must be u8/u16/u32/u64"
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure entry
      | _ => throwError "extract/unsupported: pf_svm_raw_return is not a definition"
  }

/--
Attach one exact Borsh-enum variant beneath a packed instruction tag. Variant dispatch and the
fixed-width scalar return codec are EntryAdapter schema data, allowing independent source handlers
to implement different enum shapes without protocol branches in the main emitter.
-/
initialize pfSvmRawVariantReturnAttr : ParametricAttribute SvmRawEntry ←
  registerParametricAttribute {
    name := `pf_svm_raw_variant_return
    descr := "declare an exact packed-u8 Borsh enum variant with a fixed-width return product"
    getParam := fun decl stx => do
      let values := syntaxNatLiterals stx
      unless values.size ≥ 5 do
        throwError "invalid pf_svm_raw_variant_return syntax"
      let entry : SvmRawEntry := {
        tag := values[0]!
        variant := some values[1]!
        accountCount := values[2]!
        programAccount := values[3]!
        returnWidths := values.extract 4 values.size
      }
      unless entry.tag < 256 && entry.variant.all (· < 256) do
        throwError "extract/unsupported: raw tag and Borsh variant must fit u8"
      unless 0 < entry.accountCount && entry.accountCount ≤ 64 do
        throwError "extract/unsupported: pf_svm_raw_variant_return accounts must be in 1..64"
      unless entry.programAccount < entry.accountCount do
        throwError "extract/unsupported: pf_svm_raw_variant_return program account is out of range"
      unless entry.returnWidths.all fun width =>
          width == 1 || width == 2 || width == 4 || width == 8 do
        throwError "extract/unsupported: packed returns must be u8/u16/u32/u64"
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure entry
      | _ => throwError "extract/unsupported: pf_svm_raw_variant_return is not a definition"
  }

/-- Attach one exact Borsh-enum variant with a runtime-optional fixed-width return payload. The
first result leaf is a canonical 0/1 presence flag and the listed widths cover every later leaf. -/
initialize pfSvmRawVariantOptionalReturnAttr : ParametricAttribute SvmRawEntry ←
  registerParametricAttribute {
    name := `pf_svm_raw_variant_optional_return
    descr := "declare an exact packed-u8 Borsh enum variant with an optional packed return"
    getParam := fun decl stx => do
      let values := syntaxNatLiterals stx
      unless values.size ≥ 5 do
        throwError "invalid pf_svm_raw_variant_optional_return syntax"
      let entry : SvmRawEntry := {
        tag := values[0]!
        variant := some values[1]!
        accountCount := values[2]!
        programAccount := values[3]!
        returnWidths := values.extract 4 values.size
        optionalReturnData := true
      }
      unless entry.tag < 256 && entry.variant.all (· < 256) do
        throwError "extract/unsupported: raw tag and Borsh variant must fit u8"
      unless 0 < entry.accountCount && entry.accountCount ≤ 64 do
        throwError "extract/unsupported: pf_svm_raw_variant_optional_return accounts must be in 1..64"
      unless entry.programAccount < entry.accountCount do
        throwError "extract/unsupported: pf_svm_raw_variant_optional_return program account is out of range"
      unless entry.returnWidths.all fun width =>
          width == 1 || width == 2 || width == 4 || width == 8 do
        throwError "extract/unsupported: packed return widths must be one of 1, 2, 4, or 8"
      unless entry.returnWidths.foldl (init := 0) (· + ·) ≤ 304 do
        throwError "extract/unsupported: packed return exceeds scalar scratch"
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure entry
      | _ =>
          throwError "extract/unsupported: pf_svm_raw_variant_optional_return is not a definition"
  }

def isEntry (env : Environment) (decl : Name) : Bool :=
  pfEntryAttr.hasTag env decl

def isInline (env : Environment) (decl : Name) : Bool :=
  pfInlineAttr.hasTag env decl

def isBoundary (env : Environment) (decl : Name) : Bool :=
  pfBoundaryAttr.hasTag env decl

def isNearPrivate (env : Environment) (decl : Name) : Bool :=
  pfNearPrivateAttr.hasTag env decl

def isNearPayable (env : Environment) (decl : Name) : Bool :=
  pfNearPayableAttr.hasTag env decl

def isNearVoid (env : Environment) (decl : Name) : Bool :=
  pfNearVoidAttr.hasTag env decl

def isNearPromiseOrValue (env : Environment) (decl : Name) : Bool :=
  pfNearPromiseOrValueAttr.hasTag env decl

def nearMigrationDigest? (env : Environment) (decl : Name) : Option Nat :=
  pfNearMigrateAttr.getParam? env decl

/-- Opaque source metadata. Only the NEAR target may decode these strings. -/
def nearEntryAnnotations (env : Environment) (decl : Name) : Array String := Id.run do
  let mut annotations := #[]
  if isNearPrivate env decl then
    annotations := annotations.push "near.private.v1"
  if isNearPayable env decl then
    annotations := annotations.push "near.payable.v1"
  if isNearVoid env decl then
    annotations := annotations.push "near.void.v1"
  if isNearPromiseOrValue env decl then
    annotations := annotations.push "near.promise-or-value-u128.v1"
  if let some digest := nearMigrationDigest? env decl then
    annotations := annotations.push s!"near.migrate.v1:{digest}"
  return annotations

def svmRawEntry? (env : Environment) (decl : Name) : Option SvmRawEntry :=
  pfSvmRawAttr.getParam? env decl <|> pfSvmRawBorshOptionsAttr.getParam? env decl <|>
    pfSvmRawReturnAttr.getParam? env decl <|> pfSvmRawVariantReturnAttr.getParam? env decl <|>
    pfSvmRawVariantOptionalReturnAttr.getParam? env decl

/-- Preserve all raw annotations so target projection can reject declarations that accidentally
carry more than one wire contract. -/
def svmRawEntries (env : Environment) (decl : Name) : Array SvmRawEntry := Id.run do
  let mut entries := #[]
  if let some entry := pfSvmRawAttr.getParam? env decl then
    entries := entries.push entry
  if let some entry := pfSvmRawBorshOptionsAttr.getParam? env decl then
    entries := entries.push entry
  if let some entry := pfSvmRawReturnAttr.getParam? env decl then
    entries := entries.push entry
  if let some entry := pfSvmRawVariantReturnAttr.getParam? env decl then
    entries := entries.push entry
  if let some entry := pfSvmRawVariantOptionalReturnAttr.getParam? env decl then
    entries := entries.push entry
  return entries

def SvmRawEntry.annotation (entry : SvmRawEntry) : String :=
  if entry.optionalReturnData then
    match entry.variant with
    | some variant =>
        let widths := String.intercalate "," (entry.returnWidths.map toString).toList
        s!"svm.raw.v5:{entry.tag}:{entry.accountCount}:{entry.programAccount}:{variant}:{widths}"
    | none => ""
  else if let some variant := entry.variant then
    let widths := String.intercalate "," (entry.returnWidths.map toString).toList
    s!"svm.raw.v4:{entry.tag}:{entry.accountCount}:{entry.programAccount}:{variant}:{widths}"
  else if !entry.returnWidths.isEmpty then
    let widths := String.intercalate "," (entry.returnWidths.map toString).toList
    s!"svm.raw.v3:{entry.tag}:{entry.accountCount}:{entry.programAccount}:{widths}"
  else if entry.optionWidths.isEmpty then
    s!"svm.raw.v1:{entry.tag}:{entry.accountCount}:{entry.programAccount}"
  else
    let widths := String.intercalate "," (entry.optionWidths.map toString).toList
    s!"svm.raw.v2:{entry.tag}:{entry.accountCount}:{entry.programAccount}:" ++
      s!"{entry.prefixParamCount}:{widths}"

/-- 当前环境里、恰好挂在 `ns` 下的入口（不含子名字空间）。 -/
def entriesIn (env : Environment) (ns : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if n.getPrefix == ns && isEntry env n then acc.push n else acc

end ProofForge.Attr
