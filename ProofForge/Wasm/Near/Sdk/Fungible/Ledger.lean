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

/-- Rebuild the bounded-string carrier owned by the combined JSON decoder. The decoder already
validates UTF-8, bounds `length ≤ 16`, and zeroes inactive bytes; this helper only changes the
compiler-owned frame shape needed by the event API. -/
@[pf_inline] def memoString
    (memo : ProofForge.Wasm.Near.Runtime.OptionalMemo16) :
    ProofForge.Core.Value.BoundedString 16 :=
  { length := memo.length.toUInt32
    values := #v[
      (memo.w0 &&& 0xff).toUInt8,
      ((memo.w0 >>> 8) &&& 0xff).toUInt8,
      ((memo.w0 >>> 16) &&& 0xff).toUInt8,
      ((memo.w0 >>> 24) &&& 0xff).toUInt8,
      ((memo.w0 >>> 32) &&& 0xff).toUInt8,
      ((memo.w0 >>> 40) &&& 0xff).toUInt8,
      ((memo.w0 >>> 48) &&& 0xff).toUInt8,
      ((memo.w0 >>> 56) &&& 0xff).toUInt8,
      (memo.w1 &&& 0xff).toUInt8,
      ((memo.w1 >>> 8) &&& 0xff).toUInt8,
      ((memo.w1 >>> 16) &&& 0xff).toUInt8,
      ((memo.w1 >>> 24) &&& 0xff).toUInt8,
      ((memo.w1 >>> 32) &&& 0xff).toUInt8,
      ((memo.w1 >>> 40) &&& 0xff).toUInt8,
      ((memo.w1 >>> 48) &&& 0xff).toUInt8,
      ((memo.w1 >>> 56) &&& 0xff).toUInt8] }

/-- Missing is a valid zero snapshot; a present value is valid only when its copied register fits
and is exactly the Borsh-u128 width. Nearcore raw storage statuses are closed 0/1. -/
@[pf_inline] def loadedValid : Bool :=
  let result : ResultBuffer := 16
  if result.status = 0 then true
  else if result.status = 1 then result.fits && result.length = 16
  else false

@[pf_inline] def isZero (value : ProofForge.Wasm.Near.Runtime.NearToken) : Bool :=
  value.w0 = 0 && value.w1 = 0

/-- Exact near-contract-standards resolver event memo. -/
@[pf_inline] def refundMemo : ProofForge.Core.Value.BoundedString 6 :=
  { length := 6
    values := #v[0x72, 0x65, 0x66, 0x75, 0x6e, 0x64] }

end ProofForge.Wasm.Near.Sdk.Fungible.Ledger
