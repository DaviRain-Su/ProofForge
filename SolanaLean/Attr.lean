import Lean

open Lean

namespace SolanaLean.Attr

/-- 只标记可编译根。种类由返回类型推断。 -/
initialize solanaEntryAttr : TagAttribute ←
  registerTagAttribute `solana_entry
    "mark a Lean definition as a Solana compile root"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: solana_entry is not a definition"

def isEntry (env : Environment) (decl : Name) : Bool :=
  solanaEntryAttr.hasTag env decl

/-- 当前环境里、恰好挂在 `ns` 下的入口（不含子名字空间）。 -/
def entriesIn (env : Environment) (ns : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if n.getPrefix == ns && isEntry env n then acc.push n else acc

end SolanaLean.Attr
