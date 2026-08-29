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
  { name := "XrplBal", digest := "cfae015ada92cdc9" },
  { name := "XrplBalRt", digest := "dd80a5af3243dec2" },
  { name := "XrplRoot", digest := "a8e6569035ec2d13" },
  { name := "XrplTx", digest := "2a9d4e10cd7ecec9" },
  { name := "XrplSend", digest := "64eb128e0be5a2c6" },
  { name := "XrplNest", digest := "5deed02b57389d2" }
  ]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Wasm.Xrpl.Registry