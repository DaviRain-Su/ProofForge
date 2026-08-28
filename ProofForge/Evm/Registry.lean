namespace ProofForge.Evm.Registry

/-- Source program registered for EVM builds and its canonical target-IR digest. -/
structure Entry where
  name : String
  digest : String
  deriving BEq, Repr, Inhabited

def entries : Array Entry := #[
  { name := "Counter", digest := "254202356ee921d6" },
  { name := "Pair", digest := "8a6b6ee40b8ade46" },
  { name := "Window", digest := "966cbad710c7eff1" },
  { name := "Phase", digest := "bed1d2111e652ac1" },
  { name := "Flag", digest := "6056d4920876b4f7" },
  { name := "Maybe", digest := "6b602a44477483ee" },
  { name := "EvmCtx", digest := "da71408333a778a6" },
  { name := "TipJar", digest := "754276e8063a7d08" },
  { name := "Lang", digest := "d2a43e6bf208bff0" },
  { name := "Vault", digest := "a3ea1b5b2a69c0e3" },
  { name := "Ownable", digest := "ce6397521bd115fa" },
  { name := "Token", digest := "4f1db71eb59d4254" },
  { name := "Capped", digest := "cb058e662f968f65" },
  { name := "TwoStepCounter", digest := "3b08dde14972e728" },
  { name := "Credits", digest := "2cdeb3504c14ed59" },
  { name := "Wide", digest := "692687089d4455f3" },
  { name := "Const", digest := "81830f8855cd3dda" }
]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Evm.Registry
