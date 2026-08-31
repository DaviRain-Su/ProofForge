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
  { name := "XrplSmoke", digest := "f8f474cfdfa499f6" },
  { name := "XrplGate", digest := "c2495d166a25c8e0" },
  { name := "XrplHold", digest := "e99965ac007e0da8" },
  { name := "XrplMark", digest := "20c54e937ffbf0fc" },
  { name := "XrplBal", digest := "3177150879f2b85a" },
  { name := "XrplBalRt", digest := "dd80a5af3243dec2" },
  { name := "XrplRoot", digest := "a8e6569035ec2d13" },
  { name := "XrplTx", digest := "2a9d4e10cd7ecec9" },
  { name := "XrplSend", digest := "a8e5e47454812f03" },
  { name := "XrplNest", digest := "860982785dab0d6d" },
  { name := "XrplStep", digest := "8273bd4064e4745a" },
  { name := "XrplRole", digest := "bae46704480482ee" },
  { name := "XrplPeer", digest := "b808c0cc3278fb10" },
  { name := "XrplFlag", digest := "d71a13301ce82878" },
  { name := "XrplTab", digest := "95e92ed0121f53e9" },
  { name := "XrplHand", digest := "5c6813950576cdda" },
  { name := "XrplCrew", digest := "ca03e80ef4a8218a" },
  { name := "XrplPay", digest := "5f2a9ac1b78e08de" },
  { name := "XrplMint", digest := "86625b1e737a9f82" },
  { name := "XrplLock", digest := "d2c4673c64a8d0c" },
  { name := "XrplCard", digest := "3b84bf36c5c309d7" },
  { name := "XrplVault", digest := "6b6e2791d63443d8" },
  { name := "XrplEmit", digest := "5d97e10e9319e9e1" },
  { name := "XrplTip", digest := "7e760f9ff6b668e6" },
  { name := "XrplGift", digest := "e722061475dea65e" },
  { name := "XrplCash", digest := "86367a05030e0c5a" },
  { name := "XrplBank", digest := "6a344e3db8cdf235" },
  { name := "XrplSafe", digest := "317c295ada5d467c" },
  { name := "XrplPool", digest := "57814a14c17161a5" },
  { name := "XrplFund", digest := "8cc80156ad30a85c" },
  { name := "XrplTreasury", digest := "4ace63cdcef0446b" },
  { name := "XrplToken", digest := "d03a887e6b52e7a8" },
  { name := "XrplShare", digest := "e53efc71c6393ba4" },
  { name := "XrplTake", digest := "e31f80dc4c97ee66" },
  { name := "XrplHoldEsc", digest := "2d5fcf19a07dfde1" },
  { name := "XrplVest", digest := "9ccd6e0b0e597393" },
  { name := "XrplClaim", digest := "4857c33431f624cb" },
  { name := "XrplPayout", digest := "4d769f5622556277" },
  { name := "XrplDual", digest := "d8b9fb0c4ce39299" },
  { name := "XrplLatch", digest := "d65b586272018aed" },
  { name := "XrplEscape", digest := "396ce61f0cb686e" },
  { name := "XrplFrost", digest := "28539392e2861945" },
  { name := "XrplGlaze", digest := "3775987a7dfab228" },
  { name := "XrplHinge", digest := "fa616b8741dc3412" },
  { name := "XrplBrace", digest := "d7c8b2171694729a" },
  { name := "XrplClamp", digest := "d10847e4aee069a2" },
  { name := "XrplClasp", digest := "44ca3ba8ccd77e29" },
  { name := "XrplCleft", digest := "c52ef3441e5af62a" },
  { name := "XrplClip", digest := "55c5cfabd75805bc" },
  { name := "XrplClot", digest := "3b1de560e72e534e" },
  { name := "XrplCrimp", digest := "bae04d6719fca728" },
  { name := "XrplRate", digest := "e20892eafa9b3693" },
  { name := "XrplCrate", digest := "65b2ce389bb8434" }
  ]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Wasm.Xrpl.Registry