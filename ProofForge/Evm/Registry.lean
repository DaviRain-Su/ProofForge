namespace ProofForge.Evm.Registry

/-- Source program registered for EVM builds and its canonical target-IR digest. -/
structure Entry where
  name : String
  digest : String
  deriving BEq, Repr, Inhabited

def entries : Array Entry := #[
  { name := "Counter", digest := "254202356ee921d6" },
  { name := "Pair", digest := "13af3b0dba53f17" },
  { name := "Window", digest := "966cbad710c7eff1" },
  { name := "Phase", digest := "bed1d2111e652ac1" },
  { name := "Flag", digest := "6056d4920876b4f7" },
  { name := "Maybe", digest := "6b602a44477483ee" },
  { name := "EvmCtx", digest := "3214848828e0e590" },
  { name := "TipJar", digest := "754276e8063a7d08" },
  { name := "Lang", digest := "d2a43e6bf208bff0" },
  { name := "Vault", digest := "a3ea1b5b2a69c0e3" },
  { name := "Ownable", digest := "ce6397521bd115fa" },
  { name := "Token", digest := "67a8646cba2967a6" },
  { name := "Wide", digest := "e3e24b62274618ce" },
  { name := "Const", digest := "81830f8855cd3dda" }
]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Evm.Registry
