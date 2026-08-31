namespace ProofForge.Wasm.Near.Registry

/-- Source program registered for NEAR builds and its canonical target-IR digest. -/
structure Entry where
  name : String
  digest : String
  deriving BEq, Repr, Inhabited

def entries : Array Entry := #[
  { name := "Counter", digest := "121a0c8f7e697642" },
  { name := "NearCtx", digest := "8233f27ab39f6133" },
  { name := "NearBytes", digest := "3b15034031dcf0a2" },
  { name := "NearFungibleTokenEvent", digest := "768db0d9cec95f94" },
  { name := "NearFungibleLedger", digest := "b91759b7d8a8fac7" },
  { name := "NearTokenArithmetic", digest := "f85fa4f3182ec1eb" },
  { name := "NearTokenStorage", digest := "92e4c2bf2a7f74a0" },
  { name := "NearMemory", digest := "830255873ad66d7c" },
  { name := "NearOutput", digest := "feb5dcaddfa46a16" },
  { name := "NearStorage", digest := "cd97bb762dac8be3" },
  { name := "NearStorageEconomics", digest := "9c98eca433f99470" },
  { name := "NearStorageRegistration", digest := "551039da8ad472c9" },
  { name := "NearVector", digest := "cd60fb0f3ce40ade" },
  { name := "NearLookup", digest := "d14778ca02c69012" },
  { name := "NearQueue", digest := "a8bf10c3476ef45f" },
  { name := "NearIterable", digest := "98d132f8e2c7cd5c" },
  { name := "NearPromise", digest := "6980479348d2eca3" },
  { name := "NearPromiseResult", digest := "7f65ba128b01a035" },
  { name := "NearMigration", digest := "19a760409263b854" }
]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Wasm.Near.Registry
