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
  { name := "EvmCtx", digest := "b4a1d16740330566" },
  { name := "EvmBounded", digest := "f7726cd7fe544fde" },
  { name := "EvmExceptErgonomics", digest := "8def48aa72cd2c19" },
  { name := "EvmTokenErgonomics", digest := "138c08a82e1ad205" },
  { name := "EvmSearch", digest := "1b6e78b520b5030d" },
  { name := "EvmFindIndex", digest := "18f1ba6730bc0351" },
  { name := "EvmStaticCounter", digest := "ce10997e74a7972b" },
  { name := "EvmStaticRoster", digest := "5994b0ab59e7399b" },
  { name := "EvmAggregateStorage", digest := "f66d438ad668929d" },
  { name := "EvmOrderedStorage", digest := "c37f9c0a33352f4" },
  { name := "EvmVecLog", digest := "bea39a52948599c0" },
  { name := "EvmVecStack", digest := "8903e992dacdb808" },
  { name := "GuardedPayout", digest := "359f6025f96aa432" },
  { name := "Collectible", digest := "d520f4e720c2fb7b" },
  { name := "Badge", digest := "c15c71dbbc936fc7" },
  { name := "TipJar", digest := "33bcabf27f5b9523" },
  { name := "Lang", digest := "d2a43e6bf208bff0" },
  { name := "Vault", digest := "bb2f93cb28d7501" },
  { name := "Ownable", digest := "2dc1afccaffe17c4" },
  { name := "Token", digest := "4519c849c36cc5ca" },
  { name := "Capped", digest := "bd609aceeaafd713" },
  { name := "MultiToken", digest := "c688769941bd4cfe" },
  { name := "CraftToken", digest := "2e6738a3705bc7dd" },
  { name := "TwoStepCounter", digest := "3b08dde14972e728" },
  { name := "Credits", digest := "b419d86e92ae9e9e" },
  { name := "Wide", digest := "a190f187d58d188e" },
  { name := "Const", digest := "81830f8855cd3dda" },
  { name := "EvmFeatureFlags", digest := "5cc9bb266f23487f" },
  { name := "EvmClaimBitmap", digest := "d91809979ad94cdc" },
  { name := "EvmRingMailbox", digest := "5f2a66d9732449cd" },
  { name := "EvmRingHistory", digest := "51b492f52021f6ec" },
  { name := "EvmAllowlist", digest := "5398786232c20c14" },
  { name := "EvmIdRegistry", digest := "92520ed7aaa372d0" },
  { name := "EvmConfigMap", digest := "6bcde246def26437" },
  { name := "EvmScoreMap", digest := "2f0fb0f0f9dd7663" },
  { name := "EvmCheckpointBook", digest := "ba538445e3647f45" },
  { name := "EvmCheckpointTrace", digest := "904229061bdc4a3e" },
  { name := "EvmSafeCastAccumulator", digest := "f9eb0bacf4d40cfd" },
  { name := "EvmSafeCastConfig", digest := "40d1569adcdc05a6" },
  { name := "EvmPriceBand", digest := "a7015ac3e2e471ad" },
  { name := "EvmTypedErrors", digest := "499001a31fb4d9e7" }
]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Evm.Registry
