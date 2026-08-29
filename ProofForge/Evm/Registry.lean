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
  { name := "EvmCtx", digest := "4eb0c4cd2c0b1239" },
  { name := "EvmBounded", digest := "5258e5a9356a2a9e" },
  { name := "EvmStaticCounter", digest := "ce10997e74a7972b" },
  { name := "EvmStaticRoster", digest := "5994b0ab59e7399b" },
  { name := "EvmOrderedStorage", digest := "c37f9c0a33352f4" },
  { name := "EvmVecLog", digest := "bea39a52948599c0" },
  { name := "EvmVecStack", digest := "8903e992dacdb808" },
  { name := "GuardedPayout", digest := "359f6025f96aa432" },
  { name := "Collectible", digest := "d520f4e720c2fb7b" },
  { name := "Badge", digest := "ea3aeabda40d9ffa" },
  { name := "TipJar", digest := "7928fa1163c52a21" },
  { name := "Lang", digest := "d2a43e6bf208bff0" },
  { name := "Vault", digest := "d880e1a77eca6762" },
  { name := "Ownable", digest := "bd0c554905d6547a" },
  { name := "Token", digest := "269a68fd54506509" },
  { name := "Capped", digest := "bd609aceeaafd713" },
  { name := "TwoStepCounter", digest := "3b08dde14972e728" },
  { name := "Credits", digest := "2cdeb3504c14ed59" },
  { name := "Wide", digest := "a190f187d58d188e" },
  { name := "Const", digest := "81830f8855cd3dda" }
]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Evm.Registry
