import ProofForge

namespace Examples.NearFungibleLedger

open ProofForge.Wasm.Near.Sdk
open ProofForge.Wasm.Near.Sdk.Fungible
open ProofForge.Wasm.Near.Sdk.Store
open ProofForge.Core.Value

structure State where
  supplyW0 : UInt64
  supplyW1 : UInt64
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

abbrev balances : DirectAccountNearTokenMap := 0x324c4142

@[pf_inline] private def emptyPromiseArgs : BoundedBytes 1 :=
  { length := 0, values := #v[0] }

/-- Static short fixture callback frame for sender `aa`, receiver `bb`, amount 10. Its 51 bytes fit
the existing Promise argument budget; the resolver remains dynamic through its 20 decoded leaves. -/
@[pf_inline] private def resolverCallbackArgs : BoundedBytes 51 :=
  { length := 51
    values := #v[
      0x7b, 0x22, 0x73, 0x65, 0x6e, 0x64, 0x65, 0x72, 0x5f, 0x69, 0x64, 0x22,
      0x3a, 0x22, 0x61, 0x61, 0x22,
      0x2c, 0x22, 0x72, 0x65, 0x63, 0x65, 0x69, 0x76, 0x65, 0x72, 0x5f, 0x69,
      0x64, 0x22, 0x3a, 0x22, 0x62, 0x62, 0x22, 0x2c,
      0x22, 0x61, 0x6d, 0x6f, 0x75, 0x6e, 0x74, 0x22, 0x3a, 0x22, 0x31, 0x30,
      0x22, 0x7d] }

@[pf_inline] private def resolverChildGas : UInt64 := 15_000_000_000_000
@[pf_inline] private def resolverCallbackGas : UInt64 := 30_000_000_000_000

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

/-- Public-shaped total-supply view over the closed ledger state. -/
@[pf_entry, pf_near_no_args]
def ft_total_supply (state : State) : ProofForge.Core.Value.UInt128 :=
  ⟨state.supplyW0, state.supplyW1⟩

/-- The integrated ledger's bounded NEP-148 metadata view. This fixed configured carrier satisfies
the optional near-contract-standards validator by construction; capacities remain ProofForge
product policy rather than authoritative metadata limits. -/
@[pf_entry, pf_near_no_args]
def ft_metadata (_state : State) : ProofForge.Wasm.Near.Runtime.FungibleTokenMetadataResult :=
  { nameLength := 16
    nameW0 := 0x726f46666f6f7250
    nameW1 := 0x6e656b6f54206567
    nameW2 := 0
    nameW3 := 0
    nameW4 := 0
    nameW5 := 0
    nameW6 := 0
    nameW7 := 0
    symbolLength := 2
    symbolW0 := 0x4650
    symbolW1 := 0
    iconPresent := 0
    iconLength := 0
    iconW0 := 0
    iconW1 := 0
    iconW2 := 0
    iconW3 := 0
    iconW4 := 0
    iconW5 := 0
    iconW6 := 0
    iconW7 := 0
    iconW8 := 0
    iconW9 := 0
    iconW10 := 0
    iconW11 := 0
    iconW12 := 0
    iconW13 := 0
    iconW14 := 0
    iconW15 := 0
    iconW16 := 0
    iconW17 := 0
    iconW18 := 0
    iconW19 := 0
    iconW20 := 0
    iconW21 := 0
    iconW22 := 0
    iconW23 := 0
    iconW24 := 0
    iconW25 := 0
    iconW26 := 0
    iconW27 := 0
    iconW28 := 0
    iconW29 := 0
    iconW30 := 0
    iconW31 := 0
    referencePresent := 0
    referenceLength := 0
    referenceW0 := 0
    referenceW1 := 0
    referenceW2 := 0
    referenceW3 := 0
    referenceW4 := 0
    referenceW5 := 0
    referenceW6 := 0
    referenceW7 := 0
    referenceW8 := 0
    referenceW9 := 0
    referenceW10 := 0
    referenceW11 := 0
    referenceW12 := 0
    referenceW13 := 0
    referenceW14 := 0
    referenceW15 := 0
    referenceHashPresent := 0
    referenceHashW0 := 0
    referenceHashW1 := 0
    referenceHashW2 := 0
    referenceHashW3 := 0
    decimals := 18 }

/-- Public-shaped view fixture over the closed ledger namespace. Its input grammar remains the
bounded ProofForge AccountId object subset rather than a generic near-sdk serde wrapper. -/
@[pf_entry]
def ft_balance_of (_state : State)
    (account : ProofForge.Wasm.Near.Runtime.AccountId) : ProofForge.Core.Value.UInt128 :=
  let _ := balances.read account
  ⟨ProofForge.Wasm.Near.Runtime.storageResultNearTokenW0Strict,
    ProofForge.Wasm.Near.Runtime.storageResultNearTokenW1Strict⟩

/-- Exact near-contract-standards transfer policy over the closed `BAL2` ledger. The generated
JSON input wrapper remains ProofForge's bounded canonical subset, not general serde_json. -/
@[pf_entry, pf_near_payable, pf_near_void]
def ft_transfer (state : State) (args : ProofForge.Wasm.Near.Runtime.FtTransferArgs) :
    Except Error (State × Unit) :=
  let deposit := Context.attachedDeposit
  if Registration.attachedIsOne deposit then
    let sender := Context.caller
    if !AccountId.eq sender args.receiverId then
      if !Ledger.isZero args.amount then
        let _ := balances.read sender
        if Registration.readWasValidPresent then
          let senderW0 := resultNearTokenW0D 0
          let senderW1 := resultNearTokenW1D 0
          if ProofForge.Wasm.Near.Runtime.nearTokenSubOk
              senderW0 senderW1 args.amount.w0 args.amount.w1 != 0 then
            let _ := balances.read args.receiverId
            if Registration.readWasValidPresent then
              let receiverW0 := resultNearTokenW0D 0
              let receiverW1 := resultNearTokenW1D 0
              if ProofForge.Wasm.Near.Runtime.nearTokenAddOk
                  receiverW0 receiverW1 args.amount.w0 args.amount.w1 != 0 then
                let nextSender : NearToken :=
                  ⟨ProofForge.Wasm.Near.Runtime.nearTokenSubW0
                      senderW0 senderW1 args.amount.w0 args.amount.w1,
                    ProofForge.Wasm.Near.Runtime.nearTokenSubW1
                      senderW0 senderW1 args.amount.w0 args.amount.w1⟩
                let nextReceiver : NearToken :=
                  ⟨ProofForge.Wasm.Near.Runtime.nearTokenAddW0
                      receiverW0 receiverW1 args.amount.w0 args.amount.w1,
                    ProofForge.Wasm.Near.Runtime.nearTokenAddW1
                      receiverW0 receiverW1 args.amount.w0 args.amount.w1⟩
                let senderStatus := balances.put sender nextSender
                let receiverStatus := balances.put args.receiverId nextReceiver
                if args.memo.present = 0 then
                  let _ := Events.FungibleToken.transfer sender args.receiverId args.amount
                  .ok (⟨state.supplyW0, state.supplyW1,
                    senderStatus ||| receiverStatus⟩, ())
                else
                  let _ := Events.FungibleToken.transferWithMemo sender args.receiverId args.amount
                    16 (Ledger.memoString args.memo)
                  .ok (⟨state.supplyW0, state.supplyW1,
                    senderStatus ||| receiverStatus⟩, ())
              else .error .overflow
            else .error .overflow
          else .error .overflow
        else .error .overflow
      else .error .overflow
    else .error .overflow
  else .error .overflow

/-- Promise-backed transfer-call over the same integrated `BAL2` ledger. Operation and returned
resolver semantics follow near-contract-standards; the generated argument wrapper remains the
bounded ProofForge subset rather than general serde_json. -/
@[pf_entry, pf_near_payable]
def ft_transfer_call (state : State)
    (args : ProofForge.Wasm.Near.Runtime.FtTransferCallArgs) :
    Except Error (State × UInt64) :=
  let deposit := Context.attachedDeposit
  if Registration.attachedIsOne deposit then
    let sender := Context.caller
    if !AccountId.eq sender args.receiverId then
      if !Ledger.isZero args.amount then
        let _ := balances.read sender
        if Registration.readWasValidPresent then
          let senderW0 := resultNearTokenW0D 0
          let senderW1 := resultNearTokenW1D 0
          if ProofForge.Wasm.Near.Runtime.nearTokenSubOk
              senderW0 senderW1 args.amount.w0 args.amount.w1 != 0 then
            let _ := balances.read args.receiverId
            if Registration.readWasValidPresent then
              let receiverW0 := resultNearTokenW0D 0
              let receiverW1 := resultNearTokenW1D 0
              if ProofForge.Wasm.Near.Runtime.nearTokenAddOk
                  receiverW0 receiverW1 args.amount.w0 args.amount.w1 != 0 then
                let nextSender : NearToken :=
                  ⟨ProofForge.Wasm.Near.Runtime.nearTokenSubW0
                      senderW0 senderW1 args.amount.w0 args.amount.w1,
                    ProofForge.Wasm.Near.Runtime.nearTokenSubW1
                      senderW0 senderW1 args.amount.w0 args.amount.w1⟩
                let nextReceiver : NearToken :=
                  ⟨ProofForge.Wasm.Near.Runtime.nearTokenAddW0
                      receiverW0 receiverW1 args.amount.w0 args.amount.w1,
                    ProofForge.Wasm.Near.Runtime.nearTokenAddW1
                      receiverW0 receiverW1 args.amount.w0 args.amount.w1⟩
                let senderStatus := balances.put sender nextSender
                let receiverStatus := balances.put args.receiverId nextReceiver
                let status := senderStatus ||| receiverStatus
                if args.memo.present = 0 then
                  let _ := Events.FungibleToken.transfer sender args.receiverId args.amount
                  let _ := Promises.ftOnTransferThenResolveReturned args.receiverId sender
                    args.amount args.msg
                  .ok (⟨state.supplyW0, state.supplyW1, status⟩, status)
                else
                  let _ := Events.FungibleToken.transferWithMemo sender args.receiverId args.amount
                    16 (Ledger.memoString args.memo)
                  let _ := Promises.ftOnTransferThenResolveReturned args.receiverId sender
                    args.amount args.msg
                  .ok (⟨state.supplyW0, state.supplyW1, status⟩, status)
              else .error .overflow
            else .error .overflow
          else .error .overflow
        else .error .overflow
      else .error .overflow
    else .error .overflow
  else .error .overflow

/-- Private near-contract-standards resolver semantics over the same `BAL2` balances and supply.
The callback argument and Promise-result JSON codecs are bounded canonical subsets of serde_json.
Failed or invalid child output refunds the full amount; a valid unused amount is clamped to the
original transfer. A deleted sender burns the refundable receiver balance and reports the original
amount as used, matching near-contract-standards rather than `amount - burned`. -/
@[pf_entry, pf_near_private]
def ft_resolve_transfer (state : State)
    (args : ProofForge.Wasm.Near.Runtime.FtResolveTransferArgs) :
    Except Error (State × ProofForge.Core.Value.UInt128) :=
  if Promises.resultsCount == 1 then
    let result : Promises.ResultBuffer := 41
    let _ := result.read 0
    let decoded := result.quotedU128
    let requestedW0 := if decoded.valid != 0 then decoded.w0 else args.amount.w0
    let requestedW1 := if decoded.valid != 0 then decoded.w1 else args.amount.w1
    let requestedFits := requestedW1 < args.amount.w1 ||
      (requestedW1 = args.amount.w1 && requestedW0 ≤ args.amount.w0)
    let unusedW0 := if requestedFits then requestedW0 else args.amount.w0
    let unusedW1 := if requestedFits then requestedW1 else args.amount.w1
    let _ := balances.read args.receiverId
    if Ledger.loadedValid then
      let receiverW0 := resultNearTokenW0D 0
      let receiverW1 := resultNearTokenW1D 0
      let unusedFits := unusedW1 < receiverW1 ||
        (unusedW1 = receiverW1 && unusedW0 ≤ receiverW0)
      let refundW0 := if unusedFits then unusedW0 else receiverW0
      let refundW1 := if unusedFits then unusedW1 else receiverW1
      if refundW0 = 0 && refundW1 = 0 then
        let used : NearToken :=
          ⟨ProofForge.Wasm.Near.Runtime.nearTokenSubW0
              args.amount.w0 args.amount.w1 0 0,
            ProofForge.Wasm.Near.Runtime.nearTokenSubW1
              args.amount.w0 args.amount.w1 0 0⟩
        .ok (⟨state.supplyW0, state.supplyW1, state.marker⟩,
          used)
      else if ProofForge.Wasm.Near.Runtime.nearTokenSubOk
          receiverW0 receiverW1 refundW0 refundW1 != 0 then
        let refund : NearToken := ⟨refundW0, refundW1⟩
        let nextReceiver : NearToken :=
          ⟨ProofForge.Wasm.Near.Runtime.nearTokenSubW0
              receiverW0 receiverW1 refundW0 refundW1,
            ProofForge.Wasm.Near.Runtime.nearTokenSubW1
              receiverW0 receiverW1 refundW0 refundW1⟩
        let _ := balances.read args.senderId
        if Registration.readWasValidPresent then
          let senderW0 := resultNearTokenW0D 0
          let senderW1 := resultNearTokenW1D 0
          if ProofForge.Wasm.Near.Runtime.nearTokenAddOk
              senderW0 senderW1 refund.w0 refund.w1 != 0 then
            let nextSenderW0 := ProofForge.Wasm.Near.Runtime.nearTokenAddW0
              senderW0 senderW1 refund.w0 refund.w1
            let nextSenderW1 := ProofForge.Wasm.Near.Runtime.nearTokenAddW1
              senderW0 senderW1 refund.w0 refund.w1
            let nextSender : NearToken :=
              ⟨nextSenderW0, nextSenderW1⟩
            let used : NearToken :=
              ⟨ProofForge.Wasm.Near.Runtime.nearTokenSubW0
                  args.amount.w0 args.amount.w1 refund.w0 refund.w1,
                ProofForge.Wasm.Near.Runtime.nearTokenSubW1
                  args.amount.w0 args.amount.w1 refund.w0 refund.w1⟩
            let receiverStatus := balances.put args.receiverId nextReceiver
            let senderStatus := balances.put args.senderId nextSender
            let _ := Events.FungibleToken.transferWithMemo
              args.receiverId args.senderId refund 6 Ledger.refundMemo
            .ok (⟨state.supplyW0, state.supplyW1, receiverStatus ||| senderStatus⟩, used)
          else .error .overflow
        else if Registration.readWasMissing then
          if ProofForge.Wasm.Near.Runtime.nearTokenSubOk
              state.supplyW0 state.supplyW1 refund.w0 refund.w1 != 0 then
            let nextSupply : NearToken :=
              ⟨ProofForge.Wasm.Near.Runtime.nearTokenSubW0
                  state.supplyW0 state.supplyW1 refund.w0 refund.w1,
                ProofForge.Wasm.Near.Runtime.nearTokenSubW1
                  state.supplyW0 state.supplyW1 refund.w0 refund.w1⟩
            let receiverStatus := balances.put args.receiverId nextReceiver
            let _ := Events.FungibleToken.burnWithMemo
              args.receiverId refund 6 Ledger.refundMemo
            let used : NearToken :=
              ⟨ProofForge.Wasm.Near.Runtime.nearTokenSubW0
                  args.amount.w0 args.amount.w1 0 0,
                ProofForge.Wasm.Near.Runtime.nearTokenSubW1
                  args.amount.w0 args.amount.w1 0 0⟩
            .ok (⟨nextSupply.w0, nextSupply.w1, receiverStatus⟩,
              used)
          else .error .overflow
        else .error .overflow
      else .error .overflow
    else .error .overflow
  else .error .overflow

/-! Resolver-only child and scheduling fixtures. These nonstandard entries let near-sandbox supply
a genuine Promise result to the private callback; they are not an `ft_transfer_call` export. -/

@[pf_entry] def resolverUnusedZero (_state : State) : ProofForge.Core.Value.UInt128 := ⟨0, 0⟩
@[pf_entry] def resolverUnusedThree (_state : State) : ProofForge.Core.Value.UInt128 := ⟨3, 0⟩
@[pf_entry] def resolverUnusedTwenty (_state : State) : ProofForge.Core.Value.UInt128 := ⟨20, 0⟩

@[pf_entry] def resolverUnusedMalformed (_state : State) : BoundedBytes 4 :=
  { length := 4, values := #v[0x22, 0x30, 0x31, 0x22] }

@[pf_entry] def resolverUnusedOversized (_state : State) : BoundedBytes 42 :=
  { length := 42
    values := #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

@[pf_inline] private def scheduleResolver
    (state : State) (childMethod : String) : Except Error (State × UInt64) :=
  let promise := Promises.callThenReturned
    "resolver.test.near" childMethod emptyPromiseArgs
    (⟨0, 0⟩ : NearToken) resolverChildGas
    "ft_resolve_transfer" resolverCallbackArgs
    (⟨0, 0⟩ : NearToken) resolverCallbackGas
  .ok (⟨state.supplyW0, state.supplyW1, state.marker⟩, promise)

@[pf_entry] def resolveUnusedZero (state : State) := scheduleResolver state "resolverUnusedZero"
@[pf_entry] def resolveUnusedThree (state : State) := scheduleResolver state "resolverUnusedThree"
@[pf_entry] def resolveUnusedTwenty (state : State) := scheduleResolver state "resolverUnusedTwenty"
@[pf_entry] def resolveMalformed (state : State) := scheduleResolver state "resolverUnusedMalformed"
@[pf_entry] def resolveOversized (state : State) := scheduleResolver state "resolverUnusedOversized"
@[pf_entry] def resolveFailed (state : State) := scheduleResolver state "resolverMissingMethod"

/-! Fixture-only specialized chains below use deployed receiver contracts and the production
`ft_resolve_transfer` callback over this contract's BAL2 map. They schedule no initial transfer and
intentionally do not expose `ft_transfer_call`. -/

@[pf_entry] def chainPartial (state : State)
    (msg : ProofForge.Wasm.Near.Runtime.BoundedMessage64) : Except Error (State × UInt64) :=
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨17, 0x2e6c616974726170, 0x61656e2e74736574, 0x72, 0, 0, 0, 0, 0⟩
  let _ := Promises.ftOnTransferThenResolveReturned receiver Context.caller
    (⟨10, 0⟩ : NearToken) msg
  .ok (⟨state.supplyW0, state.supplyW1, 77⟩, 77)
@[pf_entry] def chainFull (state : State)
    (msg : ProofForge.Wasm.Near.Runtime.BoundedMessage64) : Except Error (State × UInt64) :=
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨14, 0x7365742e6c6c7566, 0x7261656e2e74, 0, 0, 0, 0, 0, 0⟩
  let _ := Promises.ftOnTransferThenResolveReturned receiver Context.caller
    (⟨10, 0⟩ : NearToken) msg
  .ok (⟨state.supplyW0, state.supplyW1, 77⟩, 77)
@[pf_entry] def chainMalformed (state : State)
    (msg : ProofForge.Wasm.Near.Runtime.BoundedMessage64) : Except Error (State × UInt64) :=
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨19, 0x656d726f666c616d, 0x6e2e747365742e64, 0x726165, 0, 0, 0, 0, 0⟩
  let _ := Promises.ftOnTransferThenResolveReturned receiver Context.caller
    (⟨10, 0⟩ : NearToken) msg
  .ok (⟨state.supplyW0, state.supplyW1, 77⟩, 77)
@[pf_entry] def chainFailed (state : State)
    (msg : ProofForge.Wasm.Near.Runtime.BoundedMessage64) : Except Error (State × UInt64) :=
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨16, 0x742e64656c696166, 0x7261656e2e747365, 0, 0, 0, 0, 0, 0⟩
  let _ := Promises.ftOnTransferThenResolveReturned receiver Context.caller
    (⟨10, 0⟩ : NearToken) msg
  .ok (⟨state.supplyW0, state.supplyW1, 77⟩, 77)

@[pf_entry] def fixtureChainPartialPresent (_state : State) : Except Error (State × UInt64) :=
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨17, 0x2e6c616974726170, 0x61656e2e74736574, 0x72, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.put Context.caller ⟨2, 0⟩
  let receiverStatus := balances.put receiver ⟨7, 0⟩
  let status := senderStatus ||| receiverStatus
  .ok (⟨9, 0, status⟩, status)
@[pf_entry] def fixtureChainFullMissing (_state : State) : Except Error (State × UInt64) :=
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨14, 0x7365742e6c6c7566, 0x7261656e2e74, 0, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.remove Context.caller
  let receiverStatus := balances.put receiver ⟨7, 0⟩
  let status := senderStatus ||| receiverStatus
  .ok (⟨7, 0, status⟩, status)
@[pf_entry] def fixtureChainMalformedPresent (_state : State) : Except Error (State × UInt64) :=
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨19, 0x656d726f666c616d, 0x6e2e747365742e64, 0x726165, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.put Context.caller ⟨2, 0⟩
  let receiverStatus := balances.put receiver ⟨7, 0⟩
  let status := senderStatus ||| receiverStatus
  .ok (⟨9, 0, status⟩, status)
@[pf_entry] def fixtureChainFailedPresent (_state : State) : Except Error (State × UInt64) :=
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨16, 0x742e64656c696166, 0x7261656e2e747365, 0, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.put Context.caller ⟨2, 0⟩
  let receiverStatus := balances.put receiver ⟨7, 0⟩
  let status := senderStatus ||| receiverStatus
  .ok (⟨9, 0, status⟩, status)

/-- Seed one conserved ledger shared by the four deployed `ft_on_transfer` integration fixtures.
Each call overwrites every participating key so one asynchronous scene cannot leak into the next. -/
@[pf_entry] def fixtureTransferCall (_state : State) : Except Error (State × UInt64) :=
  let partialAccount : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨17, 0x2e6c616974726170, 0x61656e2e74736574, 0x72, 0, 0, 0, 0, 0⟩
  let full : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨14, 0x7365742e6c6c7566, 0x7261656e2e74, 0, 0, 0, 0, 0, 0⟩
  let malformed : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨19, 0x656d726f666c616d, 0x6e2e747365742e64, 0x726165, 0, 0, 0, 0, 0⟩
  let failed : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨16, 0x742e64656c696166, 0x7261656e2e747365, 0, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.put Context.caller ⟨1, 1⟩
  let partialStatus := balances.put partialAccount ⟨0, 0⟩
  let fullStatus := balances.put full ⟨0, 0⟩
  let malformedStatus := balances.put malformed ⟨0, 0⟩
  let failedStatus := balances.put failed ⟨0, 0⟩
  let status := senderStatus ||| partialStatus ||| fullStatus ||| malformedStatus ||| failedStatus
  .ok (⟨1, 1, status⟩, status)

/-- Fixture-only paid callback proves the private resolver retains the default non-payable guard. -/
@[pf_entry]
def resolvePaidCallback (state : State) : Except Error (State × UInt64) :=
  let promise := Promises.callThenReturned
    "resolver.test.near" "resolverUnusedZero" emptyPromiseArgs
    (⟨0, 0⟩ : NearToken) resolverChildGas
    "ft_resolve_transfer" resolverCallbackArgs
    (⟨1, 0⟩ : NearToken) resolverCallbackGas
  .ok (⟨state.supplyW0, state.supplyW1, state.marker⟩, promise)

/-- Self-scheduled ordinary call passes the private guard but has zero Promise results. -/
@[pf_entry]
def resolveCountZero (state : State) : Except Error (State × UInt64) :=
  let promise := Promises.callReturned "test.near" "ft_resolve_transfer" resolverCallbackArgs
    (⟨0, 0⟩ : NearToken) resolverCallbackGas
  .ok (⟨state.supplyW0, state.supplyW1, state.marker⟩, promise)

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

@[pf_entry]
def fixtureResetCaller (_state : State) : Except Error (State × UInt64) :=
  let status := balances.remove Context.caller
  .ok (⟨0, 0, status⟩, status)

/-! Resolver fixture seeds own only sandbox setup. The production-shaped resolver still uses the
same `BAL2` map and state supply and has no alternate balance namespace. -/

@[pf_entry]
def fixtureResetResolver (_state : State) : Except Error (State × UInt64) :=
  let sender : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6161, 0, 0, 0, 0, 0, 0, 0⟩
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6262, 0, 0, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.remove sender
  let receiverStatus := balances.remove receiver
  let status := senderStatus ||| receiverStatus
  .ok (⟨0, 0, status⟩, status)

@[pf_entry]
def fixtureResolverPresent (_state : State) : Except Error (State × UInt64) :=
  let sender : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6161, 0, 0, 0, 0, 0, 0, 0⟩
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6262, 0, 0, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.put sender ⟨2, 0⟩
  let receiverStatus := balances.put receiver ⟨7, 0⟩
  let status := senderStatus ||| receiverStatus
  .ok (⟨9, 0, status⟩, status)

@[pf_entry]
def fixtureResolverMissingSender (_state : State) : Except Error (State × UInt64) :=
  let sender : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6161, 0, 0, 0, 0, 0, 0, 0⟩
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6262, 0, 0, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.remove sender
  let receiverStatus := balances.put receiver ⟨7, 0⟩
  let status := senderStatus ||| receiverStatus
  .ok (⟨7, 0, status⟩, status)

@[pf_entry]
def fixtureResolverMissingReceiver (_state : State) : Except Error (State × UInt64) :=
  let sender : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6161, 0, 0, 0, 0, 0, 0, 0⟩
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6262, 0, 0, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.put sender ⟨2, 0⟩
  let receiverStatus := balances.remove receiver
  let status := senderStatus ||| receiverStatus
  .ok (⟨2, 0, status⟩, status)

@[pf_entry]
def fixtureResolverReceiverZero (_state : State) : Except Error (State × UInt64) :=
  let sender : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6161, 0, 0, 0, 0, 0, 0, 0⟩
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6262, 0, 0, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.put sender ⟨2, 0⟩
  let receiverStatus := balances.put receiver ⟨0, 0⟩
  let status := senderStatus ||| receiverStatus
  .ok (⟨2, 0, status⟩, status)

@[pf_entry]
def fixtureResolverSenderMax (_state : State) : Except Error (State × UInt64) :=
  let sender : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6161, 0, 0, 0, 0, 0, 0, 0⟩
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6262, 0, 0, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.put sender ⟨0xffffffffffffffff, 0xffffffffffffffff⟩
  let receiverStatus := balances.put receiver ⟨1, 0⟩
  let status := senderStatus ||| receiverStatus
  .ok (⟨0xffffffffffffffff, 0xffffffffffffffff, status⟩, status)

@[pf_entry]
def fixtureResolverSupplyUnderflow (_state : State) : Except Error (State × UInt64) :=
  let sender : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6161, 0, 0, 0, 0, 0, 0, 0⟩
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6262, 0, 0, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.remove sender
  let receiverStatus := balances.put receiver ⟨1, 0⟩
  let status := senderStatus ||| receiverStatus
  .ok (⟨0, 0, status⟩, status)

@[pf_entry]
def fixtureResolverMalformedReceiver (_state : State) : Except Error (State × UInt64) :=
  let sender : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6161, 0, 0, 0, 0, 0, 0, 0⟩
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6262, 0, 0, 0, 0, 0, 0, 0⟩
  let senderStatus := balances.put sender ⟨2, 0⟩
  let _ := ProofForge.Wasm.Near.Runtime.accountNearTokenFixtureWriteMalformed
    balances receiver 8
  .ok (⟨2, 0, senderStatus⟩, senderStatus)

@[pf_entry]
def fixtureResolverMalformedSender (_state : State) : Except Error (State × UInt64) :=
  let sender : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6161, 0, 0, 0, 0, 0, 0, 0⟩
  let receiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6262, 0, 0, 0, 0, 0, 0, 0⟩
  let receiverStatus := balances.put receiver ⟨1, 0⟩
  let _ := ProofForge.Wasm.Near.Runtime.accountNearTokenFixtureWriteMalformed
    balances sender 20
  .ok (⟨1, 0, receiverStatus⟩, receiverStatus)

end Examples.NearFungibleLedger
