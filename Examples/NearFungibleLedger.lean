import ProofForge

namespace Examples.NearFungibleLedger

open ProofForge.Wasm.Near.Sdk
open ProofForge.Wasm.Near.Sdk.Fungible
open ProofForge.Wasm.Near.Sdk.Store

structure State where
  supplyW0 : UInt64
  supplyW1 : UInt64
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

abbrev balances : DirectAccountNearTokenMap := 0x324c4142

@[pf_entry]
def init : State := ⟨0, 0, 0⟩

@[pf_entry]
def supplyW0 (state : State) : UInt64 := state.supplyW0

@[pf_entry]
def supplyW1 (state : State) : UInt64 := state.supplyW1

@[pf_entry]
def marker (state : State) : UInt64 := state.marker

@[pf_entry]
def get (state : State) : UInt64 := state.marker

@[pf_entry]
def balanceSelfW0 (_state : State) : UInt64 :=
  let _ := balances.read Context.self
  resultNearTokenW0D 0

@[pf_entry]
def balanceSelfW1 (_state : State) : UInt64 :=
  let _ := balances.read Context.self
  resultNearTokenW1D 0

@[pf_entry]
def balanceSelfHas (_state : State) : UInt64 := balances.has Context.self

/-- Public-shaped view fixture over the closed ledger namespace. Its input grammar remains the
bounded ProofForge AccountId object subset rather than a generic near-sdk serde wrapper. -/
@[pf_entry]
def ft_balance_of (_state : State)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : ProofForge.Core.Value.UInt128 :=
  let _ := balances.read account
  ⟨ProofForge.Wasm.Near.Runtime.storageResultNearTokenW0Strict,
    ProofForge.Wasm.Near.Runtime.storageResultNearTokenW1Strict⟩

@[pf_inline] private def mint (state : State) (owner : ProofForge.Wasm.Near.Runtime.AccountId)
    (amount : NearToken) :
    Except Error (State × UInt64) :=
  let _ := balances.read owner
  if Ledger.loadedValid then
    let balanceW0 := resultNearTokenW0D 0
    let balanceW1 := resultNearTokenW1D 0
    if ProofForge.Wasm.Near.Runtime.nearTokenAddOk
        balanceW0 balanceW1 amount.w0 amount.w1 != 0 then
      if ProofForge.Wasm.Near.Runtime.nearTokenAddOk
          state.supplyW0 state.supplyW1 amount.w0 amount.w1 != 0 then
      let nextBalance : NearToken :=
        ⟨ProofForge.Wasm.Near.Runtime.nearTokenAddW0
            balanceW0 balanceW1 amount.w0 amount.w1,
          ProofForge.Wasm.Near.Runtime.nearTokenAddW1
            balanceW0 balanceW1 amount.w0 amount.w1⟩
      let nextSupply : NearToken :=
        ⟨ProofForge.Wasm.Near.Runtime.nearTokenAddW0
            state.supplyW0 state.supplyW1 amount.w0 amount.w1,
          ProofForge.Wasm.Near.Runtime.nearTokenAddW1
            state.supplyW0 state.supplyW1 amount.w0 amount.w1⟩
      if Ledger.isZero amount then
        .ok (⟨state.supplyW0, state.supplyW1, state.marker⟩, 0)
      else
        let status := balances.put owner nextBalance
        .ok (⟨nextSupply.w0, nextSupply.w1, status⟩, status)
      else .error .overflow
    else .error .overflow
  else .error .overflow

@[pf_inline] private def burn (state : State) (owner : ProofForge.Wasm.Near.Runtime.AccountId)
    (amount : NearToken) :
    Except Error (State × UInt64) :=
  let _ := balances.read owner
  if Ledger.loadedValid then
    let balanceW0 := resultNearTokenW0D 0
    let balanceW1 := resultNearTokenW1D 0
    if ProofForge.Wasm.Near.Runtime.nearTokenSubOk
        balanceW0 balanceW1 amount.w0 amount.w1 != 0 then
      if ProofForge.Wasm.Near.Runtime.nearTokenSubOk
          state.supplyW0 state.supplyW1 amount.w0 amount.w1 != 0 then
      let nextBalance : NearToken :=
        ⟨ProofForge.Wasm.Near.Runtime.nearTokenSubW0
            balanceW0 balanceW1 amount.w0 amount.w1,
          ProofForge.Wasm.Near.Runtime.nearTokenSubW1
            balanceW0 balanceW1 amount.w0 amount.w1⟩
      let nextSupply : NearToken :=
        ⟨ProofForge.Wasm.Near.Runtime.nearTokenSubW0
            state.supplyW0 state.supplyW1 amount.w0 amount.w1,
          ProofForge.Wasm.Near.Runtime.nearTokenSubW1
            state.supplyW0 state.supplyW1 amount.w0 amount.w1⟩
      if Ledger.isZero amount then
        .ok (⟨state.supplyW0, state.supplyW1, state.marker⟩, 0)
      else
        if Ledger.isZero nextBalance then
          let status := balances.remove owner
          .ok (⟨nextSupply.w0, nextSupply.w1, status⟩, status)
        else
          let status := balances.put owner nextBalance
          .ok (⟨nextSupply.w0, nextSupply.w1, status⟩, status)
      else .error .overflow
    else .error .overflow
  else .error .overflow

@[pf_inline] private def transfer (state : State)
    (source destination : ProofForge.Wasm.Near.Runtime.AccountId) (amount : NearToken) :
    Except Error (State × UInt64) :=
  let _ := balances.read source
  if Ledger.loadedValid then
    let sourceW0 := resultNearTokenW0D 0
    let sourceW1 := resultNearTokenW1D 0
    if ProofForge.Wasm.Near.Runtime.nearTokenSubOk
        sourceW0 sourceW1 amount.w0 amount.w1 != 0 then
      if ProofForge.Wasm.Near.Sdk.AccountId.eq source destination then
        .ok (⟨state.supplyW0, state.supplyW1, state.marker⟩, 0)
      else
        let _ := balances.read destination
        if Ledger.loadedValid then
        let destinationW0 := resultNearTokenW0D 0
        let destinationW1 := resultNearTokenW1D 0
        if ProofForge.Wasm.Near.Runtime.nearTokenAddOk
            destinationW0 destinationW1 amount.w0 amount.w1 != 0 then
          if Ledger.isZero amount then
            .ok (⟨state.supplyW0, state.supplyW1, state.marker⟩, 0)
          else
          let nextSource : NearToken :=
            ⟨ProofForge.Wasm.Near.Runtime.nearTokenSubW0
                sourceW0 sourceW1 amount.w0 amount.w1,
              ProofForge.Wasm.Near.Runtime.nearTokenSubW1
                sourceW0 sourceW1 amount.w0 amount.w1⟩
          let nextDestination : NearToken :=
            ⟨ProofForge.Wasm.Near.Runtime.nearTokenAddW0
                destinationW0 destinationW1 amount.w0 amount.w1,
              ProofForge.Wasm.Near.Runtime.nearTokenAddW1
                destinationW0 destinationW1 amount.w0 amount.w1⟩
          if Ledger.isZero nextSource then
            let sourceStatus := balances.remove source
            let destinationStatus := balances.put destination nextDestination
            let status := sourceStatus ||| destinationStatus
            .ok (⟨state.supplyW0, state.supplyW1, status⟩, status)
          else
            let sourceStatus := balances.put source nextSource
            let destinationStatus := balances.put destination nextDestination
            let status := sourceStatus ||| destinationStatus
            .ok (⟨state.supplyW0, state.supplyW1, status⟩, status)
        else .error .overflow
        else .error .overflow
    else .error .overflow
  else .error .overflow

@[pf_entry] def mintSelfOne (state : State) := mint state Context.self ⟨1, 0⟩
@[pf_entry] def mintSelfTwo64 (state : State) := mint state Context.self ⟨0, 1⟩
@[pf_entry] def mintSelfMax (state : State) :=
  mint state Context.self ⟨0xffffffffffffffff, 0xffffffffffffffff⟩
@[pf_entry] def mintCallerOne (state : State) := mint state Context.caller ⟨1, 0⟩
@[pf_entry] def mintCallerTwo64 (state : State) := mint state Context.caller ⟨0, 1⟩
@[pf_entry] def mintSelfZero (state : State) := mint state Context.self ⟨0, 0⟩

@[pf_entry] def burnSelfOne (state : State) := burn state Context.self ⟨1, 0⟩
@[pf_entry] def burnSelfTwo64 (state : State) := burn state Context.self ⟨0, 1⟩
@[pf_entry] def burnSelfMax (state : State) :=
  burn state Context.self ⟨0xffffffffffffffff, 0xffffffffffffffff⟩
@[pf_entry] def burnSelfZero (state : State) := burn state Context.self ⟨0, 0⟩

@[pf_entry] def transferCallerToSelfOne (state : State) :=
  transfer state Context.caller Context.self ⟨1, 0⟩
@[pf_entry] def transferCallerToSelfTwo64 (state : State) :=
  transfer state Context.caller Context.self ⟨0, 1⟩
@[pf_entry] def transferCallerToSelfMax (state : State) :=
  transfer state Context.caller Context.self ⟨0xffffffffffffffff, 0xffffffffffffffff⟩
@[pf_entry] def transferCallerToSelfZero (state : State) :=
  transfer state Context.caller Context.self ⟨0, 0⟩

@[pf_entry]
def seedSelfMalformed8 (state : State) : Except Error (State × UInt64) :=
  let _ := ProofForge.Wasm.Near.Runtime.accountNearTokenFixtureWriteMalformed
    balances Context.self 8
  let result : ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer := 16
  let status := result.status
  .ok (⟨state.supplyW0, state.supplyW1, status⟩, status)

@[pf_entry]
def seedSelfMalformed20 (state : State) : Except Error (State × UInt64) :=
  let _ := ProofForge.Wasm.Near.Runtime.accountNearTokenFixtureWriteMalformed
    balances Context.self 20
  let result : ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer := 16
  let status := result.status
  .ok (⟨state.supplyW0, state.supplyW1, status⟩, status)

/-! The following entries are fixture-only inconsistent-state seeds. They make otherwise
unreachable overflow/underflow prechecks observable without adding a public ledger mutation ABI. -/

@[pf_entry]
def fixturePutSelfMaxNoSupply (state : State) : Except Error (State × UInt64) :=
  let status := balances.put Context.self ⟨0xffffffffffffffff, 0xffffffffffffffff⟩
  .ok (⟨state.supplyW0, state.supplyW1, status⟩, status)

@[pf_entry]
def fixturePutSelfOneNoSupply (state : State) : Except Error (State × UInt64) :=
  let status := balances.put Context.self ⟨1, 0⟩
  .ok (⟨state.supplyW0, state.supplyW1, status⟩, status)

@[pf_entry]
def fixturePutSelfZeroNoSupply (state : State) : Except Error (State × UInt64) :=
  let status := balances.put Context.self ⟨0, 0⟩
  .ok (⟨state.supplyW0, state.supplyW1, status⟩, status)

@[pf_entry]
def fixturePutShortNoSupply (state : State) : Except Error (State × UInt64) :=
  let account : ProofForge.Wasm.Near.Runtime.AccountId :=
    { length := 2, w0 := 0x6161, w1 := 0xdeadbeef, w2 := 0, w3 := 0,
      w4 := 0, w5 := 0, w6 := 0, w7 := 0xffffffffffffffff }
  let status := balances.put account ⟨3, 1⟩
  .ok (⟨state.supplyW0, state.supplyW1, status⟩, status)

@[pf_entry]
def fixturePutMaxAccountNoSupply (state : State) : Except Error (State × UInt64) :=
  let account : ProofForge.Wasm.Near.Runtime.AccountId :=
    { length := 64, w0 := 0x6867666564636261, w1 := 0x3736353433323130,
      w2 := 0x706f6e6d6c6b6a69, w3 := 0x6665646362613938,
      w4 := 0x7877767574737271, w5 := 0x3031323334353637,
      w6 := 0x6665646362617a79, w7 := 0x3736353433323130 }
  let status := balances.put account ⟨0xffffffffffffffff, 0xffffffffffffffff⟩
  .ok (⟨state.supplyW0, state.supplyW1, status⟩, status)

@[pf_entry]
def fixtureRemoveViewAccounts (state : State) : Except Error (State × UInt64) :=
  let short : ProofForge.Wasm.Near.Runtime.AccountId :=
    { length := 2, w0 := 0x6161, w1 := 0, w2 := 0, w3 := 0,
      w4 := 0, w5 := 0, w6 := 0, w7 := 0 }
  let maximum : ProofForge.Wasm.Near.Runtime.AccountId :=
    { length := 64, w0 := 0x6867666564636261, w1 := 0x3736353433323130,
      w2 := 0x706f6e6d6c6b6a69, w3 := 0x6665646362613938,
      w4 := 0x7877767574737271, w5 := 0x3031323334353637,
      w6 := 0x6665646362617a79, w7 := 0x3736353433323130 }
  let shortStatus := balances.remove short
  let maximumStatus := balances.remove maximum
  let status := shortStatus ||| maximumStatus
  .ok (⟨state.supplyW0, state.supplyW1, status⟩, status)

@[pf_entry]
def fixtureSetSupplyMax (state : State) : Except Error (State × UInt64) :=
  .ok (⟨0xffffffffffffffff, 0xffffffffffffffff, state.marker⟩, state.marker)

@[pf_entry]
def fixtureResetSelf (_state : State) : Except Error (State × UInt64) :=
  let status := balances.remove Context.self
  .ok (⟨0, 0, status⟩, status)

end Examples.NearFungibleLedger
