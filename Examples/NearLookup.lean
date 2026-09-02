import ProofForge

namespace Examples.NearLookup

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk
open ProofForge.Wasm.Near.Sdk.Storage
open ProofForge.Wasm.Near.Sdk.Store

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- N14 LookupMap Handle: bare prefix `MAP1` (`0x3150414d`). -/
@[pf_inline] def mapSlots : DirectLookupMap64.Handle :=
  DirectLookupMap64.handle 0x3150414d

/-- N14 LookupSet Handle: bare prefix `SET1` (`0x31544553`). -/
@[pf_inline] def setSlots : DirectLookupSet64.Handle :=
  DirectLookupSet64.handle 0x31544553

@[pf_entry]
def init (marker : UInt64) : State :=
  { marker }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

@[pf_entry]
def mapGet (_state : State) (key : UInt64) : UInt64 :=
  mapSlots.getD key 0

@[pf_entry]
def mapHas (_state : State) (key : UInt64) : UInt64 :=
  mapSlots.has key

@[pf_entry]
def mapPut (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let status := mapSlots.put 7 value
  .ok ({ marker := status }, status)

@[pf_entry]
def mapRemove (_state : State) : Except Error (State × UInt64) :=
  let status := mapSlots.remove 7
  .ok ({ marker := status }, status)

@[pf_entry]
def setHas (_state : State) (value : UInt64) : UInt64 :=
  setSlots.has value

@[pf_entry]
def setInsert (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let inserted := setSlots.insert value
  .ok ({ marker := inserted }, inserted)

@[pf_entry]
def setRemove (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let removed := setSlots.remove value
  .ok ({ marker := removed }, removed)

abbrev balances : DirectAccountNearTokenMap := 0x314c4142
abbrev isolatedBalances : DirectAccountNearTokenMap := 0x31544c41

@[pf_entry]
def tokenPutSelfMixed (_state : State) : Except Error (State × UInt64) :=
  let status := balances.put Context.self ⟨0x0123456789abcdef, 0xfedcba9876543210⟩
  .ok ({ marker := status }, status)

@[pf_entry]
def tokenPutSelfZero (_state : State) : Except Error (State × UInt64) :=
  let status := balances.put Context.self ⟨0, 0⟩
  .ok ({ marker := status }, status)

/-- Runtime-test-only seed for a present short value under the canonical self key. -/
@[pf_entry]
def tokenSeedSelfMalformed8 (_state : State) : Except Error (State × UInt64) :=
  let _ := ProofForge.Wasm.Near.Runtime.accountNearTokenFixtureWriteMalformed
    balances Context.self 8
  let result : ResultBuffer := 16
  let status := result.status
  .ok ({ marker := status }, status)

/-- Runtime-test-only seed for an oversized value under the canonical self key. -/
@[pf_entry]
def tokenSeedSelfMalformed20 (_state : State) : Except Error (State × UInt64) :=
  let _ := ProofForge.Wasm.Near.Runtime.accountNearTokenFixtureWriteMalformed
    balances Context.self 20
  let result : ResultBuffer := 16
  let status := result.status
  .ok ({ marker := status }, status)

@[pf_entry]
def tokenPutCallerMax (_state : State) : Except Error (State × UInt64) :=
  let status := balances.put Context.caller ⟨0xffffffffffffffff, 0xffffffffffffffff⟩
  .ok ({ marker := status }, status)

@[pf_entry]
def tokenPutShortFixture (_state : State) : Except Error (State × UInt64) :=
  let account : ProofForge.Wasm.Near.Runtime.AccountId :=
    { length := 2, w0 := 0x6161, w1 := 0, w2 := 0, w3 := 0,
      w4 := 0, w5 := 0, w6 := 0, w7 := 0 }
  let status := balances.put account ⟨0x1111111111111111, 0x2222222222222222⟩
  .ok ({ marker := status }, status)

@[pf_entry]
def tokenHasShortFixture (_state : State) : UInt64 :=
  let account : ProofForge.Wasm.Near.Runtime.AccountId :=
    { length := 2, w0 := 0x6161, w1 := 0xdeadbeef, w2 := 0, w3 := 0,
      w4 := 0, w5 := 0, w6 := 0, w7 := 0xffffffffffffffff }
  balances.has account

@[pf_entry]
def tokenReadShortW0 (_state : State) : UInt64 :=
  let account : ProofForge.Wasm.Near.Runtime.AccountId :=
    { length := 2, w0 := 0x6161, w1 := 0xdeadbeef, w2 := 0, w3 := 0,
      w4 := 0, w5 := 0, w6 := 0, w7 := 0xffffffffffffffff }
  let _ := balances.read account
  resultNearTokenW0D 0

@[pf_entry]
def tokenReadShortW1 (_state : State) : UInt64 :=
  let account : ProofForge.Wasm.Near.Runtime.AccountId :=
    { length := 2, w0 := 0x6161, w1 := 0xdeadbeef, w2 := 0, w3 := 0,
      w4 := 0, w5 := 0, w6 := 0, w7 := 0xffffffffffffffff }
  let _ := balances.read account
  resultNearTokenW1D 0

@[pf_entry]
def tokenRemoveShortFixture (_state : State) : Except Error (State × UInt64) :=
  let account : ProofForge.Wasm.Near.Runtime.AccountId :=
    { length := 2, w0 := 0x6161, w1 := 0xdeadbeef, w2 := 0, w3 := 0,
      w4 := 0, w5 := 0, w6 := 0, w7 := 0xffffffffffffffff }
  let status := balances.remove account
  .ok ({ marker := status }, status)

@[pf_entry]
def tokenHasSelf (_state : State) : UInt64 :=
  balances.has Context.self

@[pf_entry]
def tokenHasSelfIsolated (_state : State) : UInt64 :=
  isolatedBalances.has Context.self

@[pf_entry]
def tokenHasCaller (_state : State) : Except Error (State × UInt64) :=
  let value := balances.has Context.caller
  .ok ({ marker := value }, value)

@[pf_entry]
def tokenReadCallerW0 (_state : State) : Except Error (State × UInt64) :=
  let _ := balances.read Context.caller
  let value := resultNearTokenW0D 0
  .ok ({ marker := value }, value)

@[pf_entry]
def tokenReadCallerW1 (_state : State) : Except Error (State × UInt64) :=
  let _ := balances.read Context.caller
  let value := resultNearTokenW1D 0
  .ok ({ marker := value }, value)

@[pf_entry]
def tokenReadSelfStatus (_state : State) : UInt64 :=
  balances.read Context.self

@[pf_entry]
def tokenReadSelfW0 (_state : State) : UInt64 :=
  let _ := balances.read Context.self
  resultNearTokenW0D 0x1111111111111111

@[pf_entry]
def tokenReadSelfW1 (_state : State) : UInt64 :=
  let _ := balances.read Context.self
  resultNearTokenW1D 0x2222222222222222

@[pf_entry]
def tokenRemoveSelf (_state : State) : Except Error (State × UInt64) :=
  let status := balances.remove Context.self
  .ok ({ marker := status }, status)

end Examples.NearLookup
