namespace ProofForge.Svm.Registry

/-- Source program registered for SVM builds and its canonical target-IR digest. -/
structure Entry where
  name : String
  digest : String
  deriving BEq, Repr, Inhabited

def entries : Array Entry := #[
  { name := "Counter", digest := "3382e308fa0843e9" },
  { name := "Pair", digest := "d34d0fcf75d86cde" },
  { name := "Nested", digest := "f43f86aa37810a4d" },
  { name := "Tree", digest := "1d4a472be13bbdbd" },
  { name := "Flag", digest := "2d68915eefc3b1c7" },
  { name := "Maybe", digest := "7eb9e25cf2688ea0" },
  { name := "Window", digest := "8ced169c7feda94b" },
  { name := "Phase", digest := "feee6b41f8f9abb2" },
  { name := "Choice", digest := "32fdccafc715b0c1" },
  { name := "Clock", digest := "ec77f67336043047" },
  { name := "Transfer", digest := "f2da40e6199ba343" },
  { name := "Ping", digest := "2d14206f60b0cbd6" },
  { name := "Call", digest := "d61ef848389e963a" },
  { name := "Info", digest := "a4fe01bf75fee0c" },
  { name := "Peer", digest := "db69bdf1efa1011d" },
  { name := "Pda", digest := "62a5beebccef3f64" },
  { name := "Signed", digest := "916df13d8e75540c" },
  { name := "Create", digest := "ae81054e874be24f" },
  { name := "TokenXfer", digest := "c9edc88528b425dd" },
  { name := "Ata", digest := "574dc90c21ca9723" },
  { name := "Rent", digest := "3933b05deb19a960" },
  { name := "TokenMint", digest := "f7535d90750f9692" },
  { name := "SysAlloc", digest := "dbb2269b9ac57a3" },
  { name := "TokenAcc", digest := "53013fc1bc2e0753" },
  { name := "Memo", digest := "26a3540da902ccb5" },
  { name := "CreatePda", digest := "403b2e609334f1ee" },
  { name := "TokenApprove", digest := "e99f2008d320e15c" },
  { name := "TokenFreeze", digest := "6d4fceb52be9cf0a" },
  { name := "TokenAuth", digest := "bf3d403346f51b82" },
  { name := "Epoch", digest := "61b060f6ce59a763" },
  { name := "TokenSize", digest := "fa48e892121ea415" },
  { name := "SysSeed", digest := "490cec59af518f0c" },
  { name := "SysXfer", digest := "906efee37227cb35" },
  { name := "TokenMint2", digest := "89ae474933102cb4" },
  { name := "TokenNative", digest := "5bc920f79c3711f0" },
  { name := "Hash", digest := "2fb59b956afdf97f" },
  { name := "Keys", digest := "b91c2a143e8ff667" },
  { name := "Keccak", digest := "9c6001a9b0534a0a" },
  { name := "Trio", digest := "70a856aa47c693d9" },
  { name := "Gate", digest := "58eb892388480134" },
  { name := "Nonce", digest := "5746ebbdd382bd56" },
  { name := "TokenOwner", digest := "d29884f00e7311b7" },
  { name := "TokenMs", digest := "672b83a54f057f79" },
  { name := "Phoenix", digest := "ce87e4ffbed91357" },
  { name := "Book", digest := "132daeadea663503" },
  { name := "Seat", digest := "54857e74b2565c94" },
  { name := "Lang", digest := "d6b504501a4879be" }
]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Svm.Registry
