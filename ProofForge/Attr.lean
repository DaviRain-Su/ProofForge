import Lean

open Lean

namespace ProofForge.Attr

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

def isEntry (env : Environment) (decl : Name) : Bool :=
  pfEntryAttr.hasTag env decl

def isInline (env : Environment) (decl : Name) : Bool :=
  pfInlineAttr.hasTag env decl

/-- 当前环境里、恰好挂在 `ns` 下的入口（不含子名字空间）。 -/
def entriesIn (env : Environment) (ns : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if n.getPrefix == ns && isEntry env n then acc.push n else acc

end ProofForge.Attr
