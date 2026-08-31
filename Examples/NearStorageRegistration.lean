import ProofForge

namespace Examples.NearStorageRegistration

open ProofForge.Wasm.Near.Sdk
open ProofForge.Wasm.Near.Sdk.Fungible
open ProofForge.Wasm.Near.Sdk.Store

structure State where
  perByteCostW0 : UInt64
  perByteCostW1 : UInt64
  lastDelta : UInt64
  lastCostW0 : UInt64
  lastCostW1 : UInt64
  lastCode : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-! This prefix deliberately matches the closed ledger fixture's balance namespace. A present zero
balance is registration; the ledger itself still does not enforce that policy. -/
abbrev registrations : DirectAccountNearTokenMap := 0x324c4142

/-- Fixture configuration boundary. The scalar supplies the low limb and its top bit expands to the
high limb: `1` selects one yoctoNEAR per byte, max-u64 selects max-u128 for overflow rollback tests,
and `0` selects the rejected zero-cost profile. The resulting trusted value is immutable and is not
a nearcore host import. -/
@[pf_entry]
def init (costProfile : UInt64) : State :=
  ⟨costProfile, (0 : UInt64) - (costProfile >>> 63), 0, 0, 0, 0⟩

@[pf_entry] def get (state : State) : UInt64 := state.lastCode
@[pf_entry] def perByteCostW0 (state : State) : UInt64 := state.perByteCostW0
@[pf_entry] def perByteCostW1 (state : State) : UInt64 := state.perByteCostW1
@[pf_entry] def lastDelta (state : State) : UInt64 := state.lastDelta
@[pf_entry] def lastCostW0 (state : State) : UInt64 := state.lastCostW0
@[pf_entry] def lastCostW1 (state : State) : UInt64 := state.lastCostW1

@[pf_entry]
def probeCaller (state : State) : Except Error (State × UInt64) :=
  let status := registrations.has Context.caller
  .ok (⟨state.perByteCostW0, state.perByteCostW1, state.lastDelta,
    state.lastCostW0, state.lastCostW1, status⟩, status)

@[pf_entry]
def probeCallerBalanceW0 (state : State) : Except Error (State × UInt64) :=
  let _ := registrations.read Context.caller
  let value := resultNearTokenW0D 0
  .ok (⟨state.perByteCostW0, state.perByteCostW1, state.lastDelta,
    state.lastCostW0, state.lastCostW1, value⟩, value)

@[pf_entry]
def probeCallerBalanceW1 (state : State) : Except Error (State × UInt64) :=
  let _ := registrations.read Context.caller
  let value := resultNearTokenW1D 0
  .ok (⟨state.perByteCostW0, state.perByteCostW1, state.lastDelta,
    state.lastCostW0, state.lastCostW1, value⟩, value)

/-- Register only the immediate caller as a present-zero balance.

The exact variable-length key cost is unknowable until nearcore performs the write, so insertion is
speculative. Every subsequent failure is a panic and relies on the executing receipt's atomic
rollback to remove that key, restore usage/balance/state, and discard staged receipts. A valid
duplicate performs no write and refunds its entire attached deposit. A new registration retains its
own measured `storage_usage` delta times the immutable configured price and refunds only excess. -/
@[pf_entry, pf_near_payable]
def registerCaller (state : State) : Except Error (State × UInt64) :=
  let caller := Context.caller
  let perByteCost : NearToken := ⟨state.perByteCostW0, state.perByteCostW1⟩
  if DirectAccountNearTokenMap.accountLengthValid caller then
    if Registration.trustedCostValid perByteCost then
      let _ := registrations.read caller
      if Registration.readWasMissing then
        let before := ProofForge.Wasm.Near.Runtime.storageUsage
        let writeStatus := registrations.put caller (⟨0, 0⟩ : NearToken)
        if writeStatus ≤ 1 then
          let after := ProofForge.Wasm.Near.Runtime.storageUsage
          if Registration.usageDeltaValid before after then
            let delta := after - before
            if NearToken.canMulUInt64 perByteCost delta then
              let cost : NearToken :=
                ⟨NearToken.mulUInt64W0 perByteCost delta,
                  NearToken.mulUInt64W1 perByteCost delta⟩
              let deposit := Context.attachedDeposit
              if Registration.depositCovers deposit cost then
                let excess : NearToken :=
                  ⟨NearToken.subW0 deposit cost, NearToken.subW1 deposit cost⟩
                if Registration.tokenIsZero excess then
                  .ok (⟨state.perByteCostW0, state.perByteCostW1,
                    delta, cost.w0, cost.w1, delta⟩, delta)
                else
                  let _ := Promises.transferAccountDetached caller excess
                  .ok (⟨state.perByteCostW0, state.perByteCostW1,
                    delta, cost.w0, cost.w1, delta⟩, delta)
              else .error .overflow
            else .error .overflow
          else .error .overflow
        else .error .overflow
      else if Registration.readWasValidPresent then
        let deposit := Context.attachedDeposit
        if Registration.tokenIsZero deposit then
          .ok (⟨state.perByteCostW0, state.perByteCostW1, state.lastDelta,
            state.lastCostW0, state.lastCostW1, state.lastCode⟩, state.lastCode)
        else
          let _ := Promises.transferAccountDetached caller deposit
          .ok (⟨state.perByteCostW0, state.perByteCostW1, state.lastDelta,
            state.lastCostW0, state.lastCostW1, state.lastCode⟩, state.lastCode)
      else .error .overflow
    else .error .overflow
  else .error .overflow

/-! Fixture-only malformed-value seed/removal paths. They expose fail-closed descriptor behavior
without extending the SDK registration contract. -/

@[pf_entry]
def seedCallerMalformed8 (state : State) : Except Error (State × UInt64) :=
  let _ := ProofForge.Wasm.Near.Runtime.accountNearTokenFixtureWriteMalformed
    registrations Context.caller 8
  let result : ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer := 16
  let status := result.status
  .ok (⟨state.perByteCostW0, state.perByteCostW1, state.lastDelta,
    state.lastCostW0, state.lastCostW1, status⟩, status)

@[pf_entry]
def fixtureRemoveCaller (state : State) : Except Error (State × UInt64) :=
  let status := registrations.remove Context.caller
  .ok (⟨state.perByteCostW0, state.perByteCostW1, 0, 0, 0, status⟩, status)

end Examples.NearStorageRegistration
