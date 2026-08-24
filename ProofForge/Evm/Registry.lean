namespace ProofForge.Evm.Registry

/-- Source program registered for EVM builds and its canonical target-IR digest. -/
structure Entry where
  name : String
  digest : String
  deriving BEq, Repr, Inhabited

def entries : Array Entry := #[
  { name := "Counter", digest := "254202356ee921d6" },
  { name := "Pair", digest := "efb8159513508e49" },
  { name := "Window", digest := "dfe0620770ff04d4" },
  { name := "Phase", digest := "5da5688932fbb630" },
  { name := "Flag", digest := "f59454e5e4736334" },
  { name := "Maybe", digest := "842f2a30ab664aac" },
  { name := "EvmCtx", digest := "d32b3b41290088b3" },
  { name := "TipJar", digest := "54e2ac6083d0820b" },
  { name := "Lang", digest := "e0e6dafdfef6d142" },
  { name := "Vault", digest := "afd331572631e6e2" },
  { name := "Ownable", digest := "7dc4a3ba2bb470b2" },
  { name := "Token", digest := "8db43ef123b7e9a9" }
]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Evm.Registry
