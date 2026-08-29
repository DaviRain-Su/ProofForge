namespace ProofForge.Wasm.Near.Registry

/-- Source program registered for NEAR builds and its canonical target-IR digest. -/
structure Entry where
  name : String
  digest : String
  deriving BEq, Repr, Inhabited

def entries : Array Entry := #[
  { name := "Counter", digest := "121a0c8f7e697642" },
  { name := "NearCtx", digest := "2030160107539932" }
]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Wasm.Near.Registry
