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
  /-- A fixed-width prefix followed by Borsh `Option<T>` fields. Each option lowers to two method
  parameters: a u8 presence flag and a scalar payload of the declared width. Empty means the
  original exact fixed-width adapter. -/
  prefixParamCount : Nat := 0
  optionWidths : Array Nat := #[]
  /-- Exact little-endian widths for a statically shaped return product. Empty retains the normal
  consecutive-u64 return ABI. This is wire metadata, not an executable operation. -/
  returnWidths : Array Nat := #[]
  deriving BEq, Repr, Inhabited

syntax (name := pf_svm_raw)
  "pf_svm_raw" num num num : attr

syntax (name := pf_svm_raw_borsh_options)
  "pf_svm_raw_borsh_options" num num num num "[" num,* "]" : attr

syntax (name := pf_svm_raw_return)
  "pf_svm_raw_return" num num num "[" num,* "]" : attr

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

def isEntry (env : Environment) (decl : Name) : Bool :=
  pfEntryAttr.hasTag env decl

def isInline (env : Environment) (decl : Name) : Bool :=
  pfInlineAttr.hasTag env decl

def svmRawEntry? (env : Environment) (decl : Name) : Option SvmRawEntry :=
  pfSvmRawAttr.getParam? env decl <|> pfSvmRawBorshOptionsAttr.getParam? env decl <|>
    pfSvmRawReturnAttr.getParam? env decl

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
  return entries

def SvmRawEntry.annotation (entry : SvmRawEntry) : String :=
  if !entry.returnWidths.isEmpty then
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
