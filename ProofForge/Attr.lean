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
  deriving BEq, Repr, Inhabited

syntax (name := pf_svm_raw)
  "pf_svm_raw" num num num : attr

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

def isEntry (env : Environment) (decl : Name) : Bool :=
  pfEntryAttr.hasTag env decl

def isInline (env : Environment) (decl : Name) : Bool :=
  pfInlineAttr.hasTag env decl

def svmRawEntry? (env : Environment) (decl : Name) : Option SvmRawEntry :=
  pfSvmRawAttr.getParam? env decl

def SvmRawEntry.annotation (entry : SvmRawEntry) : String :=
  s!"svm.raw.v1:{entry.tag}:{entry.accountCount}:{entry.programAccount}"

/-- 当前环境里、恰好挂在 `ns` 下的入口（不含子名字空间）。 -/
def entriesIn (env : Environment) (ns : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if n.getPrefix == ns && isEntry env n then acc.push n else acc

end ProofForge.Attr
