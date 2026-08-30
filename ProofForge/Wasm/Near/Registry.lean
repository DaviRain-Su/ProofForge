namespace ProofForge.Wasm.Near.Registry

/-- Source program registered for NEAR builds and its canonical target-IR digest. -/
structure Entry where
  name : String
  digest : String
  deriving BEq, Repr, Inhabited

def entries : Array Entry := #[
  { name := "Counter", digest := "121a0c8f7e697642" },
  { name := "NearCtx", digest := "8233f27ab39f6133" },
  { name := "NearBytes", digest := "97376ce24f4c70a0" },
  { name := "NearMemory", digest := "830255873ad66d7c" },
  { name := "NearOutput", digest := "d455a43be10516e3" },
  { name := "NearStorage", digest := "81dd911358e341be" },
  { name := "NearVector", digest := "25b961c16db0bb93" },
  { name := "NearLookup", digest := "153fe4dc7e95c3f0" },
  { name := "NearQueue", digest := "f04d9a0d673b7fed" },
  { name := "NearIterable", digest := "8c0ece42e2b091ff" },
  { name := "NearPromise", digest := "7ba98f4624b9cd34" },
  { name := "NearPromiseResult", digest := "ff7ea8988ba01999" }
]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Wasm.Near.Registry
