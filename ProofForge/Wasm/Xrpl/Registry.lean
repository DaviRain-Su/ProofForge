namespace ProofForge.Wasm.Xrpl.Registry

/-- Source program registered for XRPL Bedrock builds and its canonical target-IR digest. -/
structure Entry where
  name : String
  digest : String
  deriving BEq, Repr, Inhabited

def entries : Array Entry := #[
  { name := "Counter", digest := "e029f72296e320be" },
  { name := "XrplCtx", digest := "f483be9d20810b57" },
  { name := "XrplOwn", digest := "d452894f75c0ff96" },
  { name := "XrplHash", digest := "ce42ea8b4607843e" },
  { name := "XrplRt2", digest := "1d6d712500b8daf0" },
  { name := "XrplVec", digest := "e47db263444f8c7e" },
  { name := "XrplSmoke", digest := "f8f474cfdfa499f6" }
  ]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Wasm.Xrpl.Registry