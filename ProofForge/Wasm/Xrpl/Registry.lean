namespace ProofForge.Wasm.Xrpl.Registry

/-- Source program registered for XRPL Bedrock builds and its canonical target-IR digest. -/
structure Entry where
  name : String
  digest : String
  deriving BEq, Repr, Inhabited

def entries : Array Entry := #[
  { name := "Counter", digest := "e029f72296e320be" },
  { name := "XrplCtx", digest := "f483be9d20810b57" },
  { name := "XrplOwn", digest := "47645ee35068637f" }
]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Wasm.Xrpl.Registry