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
  { name := "NearFungibleLedger", digest := "f45af507fc51f527" },
  { name := "NearTokenArithmetic", digest := "f85fa4f3182ec1eb" },
  { name := "NearTokenStorage", digest := "92e4c2bf2a7f74a0" },
  { name := "NearMemory", digest := "830255873ad66d7c" },
  { name := "NearOutput", digest := "aef385d73b807e1f" },
  { name := "NearStorageBalanceOutput", digest := "b2d60a785206c3ea" },
  { name := "NearJsonUnitOutput", digest := "8c2a34289ce004b8" },
  { name := "NearJsonU128Mutation", digest := "4a2276146b03644d" },
  { name := "NearJsonAccountInput", digest := "94c66ff0e540880f" },
  { name := "NearJsonAmountInput", digest := "39187c79765d79a8" },
  { name := "NearJsonMemoInput", digest := "f3fa980c281bf1e6" },
  { name := "NearJsonMessageInput", digest := "6c9214fea46b5772" },
  { name := "NearJsonFtTransferInput", digest := "21ac8e6e13ab0ef8" },
  { name := "NearJsonFtTransferCallInput", digest := "c634c3a5c29242eb" },
  { name := "NearJsonFtOnTransferInput", digest := "8a74f45cfcf09b58" },
  { name := "NearFtReceiverValue", digest := "bb2ba467b434d5d8" },
  { name := "NearPromiseOrValue", digest := "dc1a13ff32595de5" },
  { name := "NearFtReceiverDual", digest := "d03ecd932c8aebc0" },
  { name := "NearJsonFtResolveInput", digest := "f16d9836431a6bb0" },
  { name := "NearStorage", digest := "cd97bb762dac8be3" },
  { name := "NearStorageEconomics", digest := "9c98eca433f99470" },
  { name := "NearStorageRegistration", digest := "d15fa3f4bcdbdfe" },
  { name := "NearVector", digest := "cd60fb0f3ce40ade" },
  { name := "NearLookup", digest := "d14778ca02c69012" },
  { name := "NearQueue", digest := "a8bf10c3476ef45f" },
  { name := "NearIterable", digest := "98d132f8e2c7cd5c" },
  { name := "NearPromise", digest := "e51b20dad70b3a29" },
  { name := "NearPromiseResult", digest := "7f65ba128b01a035" },
  { name := "NearMigration", digest := "19a760409263b854" }
]

def names : Array String := entries.map (·.name)

def digestOf (name : String) : Option String :=
  (entries.find? (·.name == name)).map (·.digest)

end ProofForge.Wasm.Near.Registry
