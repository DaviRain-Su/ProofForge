import ProofForge.Attr
import ProofForge.Wasm.Near.Sdk.Store.AccountTokenLookup

/-!
# Closed fungible ledger snapshot helpers

These helpers interpret the one active exact-16-byte storage result after a
`DirectAccountNearTokenMap.read`. They perform no host call: consumers must read once, snapshot both
limbs before another storage operation, complete every business check, and only then mutate.
-/

namespace ProofForge.Wasm.Near.Sdk.Fungible.Ledger

open ProofForge.Wasm.Near.Sdk.Storage
open ProofForge.Wasm.Near.Sdk.Store

/-- Missing is a valid zero snapshot; a present value is valid only when its copied register fits
and is exactly the Borsh-u128 width. Nearcore raw storage statuses are closed 0/1. -/
@[pf_inline] def loadedValid : Bool :=
  let result : ResultBuffer := 16
  if result.status = 0 then true
  else if result.status = 1 then result.fits && result.length = 16
  else false

@[pf_inline] def isZero (value : ProofForge.Wasm.Near.Runtime.NearToken) : Bool :=
  value.w0 = 0 && value.w1 = 0

end ProofForge.Wasm.Near.Sdk.Fungible.Ledger
