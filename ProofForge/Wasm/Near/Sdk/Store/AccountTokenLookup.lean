import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Wasm.Near.Runtime
import ProofForge.Wasm.Near.Sdk.Store.Codec

/-!
# Direct AccountId-to-NearToken Identity lookup

This closed map uses the legacy/current default-Identity near-sdk-rs bytes for the selected types:
`Prefix4 || Borsh(AccountId)` keys and exact Borsh `u128` values. It writes immediately and does
not model Rust cache/Drop timing, arbitrary keys/values, custom hashers, iteration, or a FT ledger.

AccountIds supplied by NEAR context hosts are nominally valid and have length 2..64. This map
preserves that contract but does not revalidate AccountId syntax for manually constructed values.
-/

namespace ProofForge.Wasm.Near.Sdk.Store

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk.Storage

/-- Compile-time four-byte Identity namespace for AccountId-to-NearToken entries. -/
abbrev DirectAccountNearTokenMap := UInt64

def DirectAccountNearTokenMap.wellFormed (map : DirectAccountNearTokenMap) : Bool :=
  map ≤ 0xffffffff

def DirectAccountNearTokenMap.accountLengthValid
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : Bool :=
  2 ≤ account.length && account.length ≤ 64

@[pf_inline] def DirectAccountNearTokenMap.bounded (tag : UInt64) : DirectAccountNearTokenMap :=
  tag

/-- Exact `prefix4 || u32_le(length) || active account bytes`. Capacity 72 holds the maximum;
raw storage staging writes only the runtime `8 + account.length` active prefix. -/
def DirectAccountNearTokenMap.elementKey (map : DirectAccountNearTokenMap)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : BoundedBytes 72 :=
  let p := map
  let n := account.length
  { length := (n + 8).toUInt32
    values := #v[
      (p &&& 0xff).toUInt8, ((p >>> 8) &&& 0xff).toUInt8,
      ((p >>> 16) &&& 0xff).toUInt8, ((p >>> 24) &&& 0xff).toUInt8,
      (n &&& 0xff).toUInt8, ((n >>> 8) &&& 0xff).toUInt8,
      ((n >>> 16) &&& 0xff).toUInt8, ((n >>> 24) &&& 0xff).toUInt8,
      (account.w0 &&& 0xff).toUInt8, ((account.w0 >>> 8) &&& 0xff).toUInt8,
      ((account.w0 >>> 16) &&& 0xff).toUInt8, ((account.w0 >>> 24) &&& 0xff).toUInt8,
      ((account.w0 >>> 32) &&& 0xff).toUInt8, ((account.w0 >>> 40) &&& 0xff).toUInt8,
      ((account.w0 >>> 48) &&& 0xff).toUInt8, ((account.w0 >>> 56) &&& 0xff).toUInt8,
      (account.w1 &&& 0xff).toUInt8, ((account.w1 >>> 8) &&& 0xff).toUInt8,
      ((account.w1 >>> 16) &&& 0xff).toUInt8, ((account.w1 >>> 24) &&& 0xff).toUInt8,
      ((account.w1 >>> 32) &&& 0xff).toUInt8, ((account.w1 >>> 40) &&& 0xff).toUInt8,
      ((account.w1 >>> 48) &&& 0xff).toUInt8, ((account.w1 >>> 56) &&& 0xff).toUInt8,
      (account.w2 &&& 0xff).toUInt8, ((account.w2 >>> 8) &&& 0xff).toUInt8,
      ((account.w2 >>> 16) &&& 0xff).toUInt8, ((account.w2 >>> 24) &&& 0xff).toUInt8,
      ((account.w2 >>> 32) &&& 0xff).toUInt8, ((account.w2 >>> 40) &&& 0xff).toUInt8,
      ((account.w2 >>> 48) &&& 0xff).toUInt8, ((account.w2 >>> 56) &&& 0xff).toUInt8,
      (account.w3 &&& 0xff).toUInt8, ((account.w3 >>> 8) &&& 0xff).toUInt8,
      ((account.w3 >>> 16) &&& 0xff).toUInt8, ((account.w3 >>> 24) &&& 0xff).toUInt8,
      ((account.w3 >>> 32) &&& 0xff).toUInt8, ((account.w3 >>> 40) &&& 0xff).toUInt8,
      ((account.w3 >>> 48) &&& 0xff).toUInt8, ((account.w3 >>> 56) &&& 0xff).toUInt8,
      (account.w4 &&& 0xff).toUInt8, ((account.w4 >>> 8) &&& 0xff).toUInt8,
      ((account.w4 >>> 16) &&& 0xff).toUInt8, ((account.w4 >>> 24) &&& 0xff).toUInt8,
      ((account.w4 >>> 32) &&& 0xff).toUInt8, ((account.w4 >>> 40) &&& 0xff).toUInt8,
      ((account.w4 >>> 48) &&& 0xff).toUInt8, ((account.w4 >>> 56) &&& 0xff).toUInt8,
      (account.w5 &&& 0xff).toUInt8, ((account.w5 >>> 8) &&& 0xff).toUInt8,
      ((account.w5 >>> 16) &&& 0xff).toUInt8, ((account.w5 >>> 24) &&& 0xff).toUInt8,
      ((account.w5 >>> 32) &&& 0xff).toUInt8, ((account.w5 >>> 40) &&& 0xff).toUInt8,
      ((account.w5 >>> 48) &&& 0xff).toUInt8, ((account.w5 >>> 56) &&& 0xff).toUInt8,
      (account.w6 &&& 0xff).toUInt8, ((account.w6 >>> 8) &&& 0xff).toUInt8,
      ((account.w6 >>> 16) &&& 0xff).toUInt8, ((account.w6 >>> 24) &&& 0xff).toUInt8,
      ((account.w6 >>> 32) &&& 0xff).toUInt8, ((account.w6 >>> 40) &&& 0xff).toUInt8,
      ((account.w6 >>> 48) &&& 0xff).toUInt8, ((account.w6 >>> 56) &&& 0xff).toUInt8,
      (account.w7 &&& 0xff).toUInt8, ((account.w7 >>> 8) &&& 0xff).toUInt8,
      ((account.w7 >>> 16) &&& 0xff).toUInt8, ((account.w7 >>> 24) &&& 0xff).toUInt8,
      ((account.w7 >>> 32) &&& 0xff).toUInt8, ((account.w7 >>> 40) &&& 0xff).toUInt8,
      ((account.w7 >>> 48) &&& 0xff).toUInt8, ((account.w7 >>> 56) &&& 0xff).toUInt8
    ] }

/-- Read once into the active exact-16-byte result buffer. Consume both limbs with the shared
`resultNearTokenW0D/W1D` decoders before issuing another storage operation. -/
def DirectAccountNearTokenMap.read (map : DirectAccountNearTokenMap)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : UInt64 :=
  let result : ResultBuffer := 16
  let _ := ProofForge.Wasm.Near.Runtime.accountNearTokenRead map account
  result.status

def DirectAccountNearTokenMap.has (map : DirectAccountNearTokenMap)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : UInt64 :=
  let result : ResultBuffer := 16
  let _ := ProofForge.Wasm.Near.Runtime.accountNearTokenHasKey map account
  result.status

/-- Immediate exact Borsh-u128 write; 0 means insert and 1 replacement. Zero is a present value. -/
def DirectAccountNearTokenMap.put (map : DirectAccountNearTokenMap)
    (account : ProofForge.Wasm.Near.Runtime.AccountId)
    (value : ProofForge.Wasm.Near.Runtime.NearToken) : UInt64 :=
  let result : ResultBuffer := 16
  let _ := ProofForge.Wasm.Near.Runtime.accountNearTokenWrite map account value
  result.status

/-- Immediate removal; 0 means absent and 1 present. -/
def DirectAccountNearTokenMap.remove (map : DirectAccountNearTokenMap)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : UInt64 :=
  let result : ResultBuffer := 16
  let _ := ProofForge.Wasm.Near.Runtime.accountNearTokenRemove map account
  result.status

end ProofForge.Wasm.Near.Sdk.Store
