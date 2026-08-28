import ProofForge

namespace Examples.Token

open ProofForge.Evm.Sdk

/-- `paused` is 0 while running and 1 while paused. The owner is a constructor immutable;
`cap` and `supply` use ordinary state slots, while balances, allowances, and nonces use maps. -/
structure State where
  dummy : UInt64
  paused : UInt8
  cap : UInt256
  supply : UInt256
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

structure ContractStorage where
  balances : Fungible.Balances
  allowances : Fungible.Allowances
  nonces : Storage.AddressMap256

attribute [pf_inline]
  ContractStorage.balances ContractStorage.allowances ContractStorage.nonces

/-- The static cursor assigns disjoint map namespaces; no numeric slot escapes into contract code. -/
@[pf_inline] def storage : ContractStorage :=
  { balances := Storage.Layout.root.addressMap256 |>.handle
    allowances := Storage.Layout.root.addressMap256 |>.next |>.addressPairMap256 |>.handle
    nonces := Storage.Layout.root.addressMap256 |>.next |>.addressPairMap256 |>.next
      |>.addressMap256 |>.handle }

@[pf_entry]
def init (_owner : Address) : State :=
  { dummy := 0, paused := 0, cap := ⟨1000, 0, 0, 0⟩, supply := UInt256.zero }

/-- Owner-only mint. Paused, zero-address, and cap failures revert without changing state. -/
@[pf_entry]
def mint (s : State) (to : Address) (value : UInt256) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    if s.paused != 0 then
      .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
        Revert.paused)
    else if Address.isZero to then
      .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
        Revert.zeroAddress)
    else if UInt256.atLeast s.cap s.supply &&
        UInt256.atLeast (UInt256.sub s.cap s.supply) value then
      if Fungible.Balances.canCredit storage.balances to value then
        .ok ({ dummy := Fungible.Balances.credit storage.balances to value,
               paused := s.paused, cap := s.cap, supply := UInt256.add s.supply value },
          Event.transfer Address.zero to value)
      else
        .error .overflow
    else
      .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
        Revert.capExceeded)
  else
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.unauthorized Context.caller)

@[pf_entry]
def balanceOf (_s : State) (who : Address) : UInt256 :=
  Fungible.Balances.balanceOf storage.balances who

@[pf_entry]
def totalSupply (s : State) : UInt256 :=
  s.supply

@[pf_entry]
def capOf (s : State) : UInt256 :=
  s.cap

@[pf_entry]
def decimals (_s : State) : UInt8 :=
  18

@[pf_entry]
def name (_s : State) : Bytes32 :=
  ⟨0, 0, 0, 0x6e656b6f54000000⟩

@[pf_entry]
def symbol (_s : State) : Bytes32 :=
  ⟨0, 0, 0, 0x4650000000000000⟩

@[pf_entry]
def allowanceOf (_s : State) (owner spender : Address) : UInt256 :=
  Fungible.Allowances.allowanceOf storage.allowances owner spender

@[pf_entry]
def nonceOf (_s : State) (who : Address) : UInt256 :=
  storage.nonces.get who

@[pf_entry]
def DOMAIN_SEPARATOR (_s : State) : Bytes32 :=
  Permit.domainSeparator

@[pf_entry]
def permit (s : State) (owner spender : Address) (value deadline : UInt256)
    (v : UInt8) (r signature : Bytes32) : Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.paused)
  else if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Permit.authorize owner spender value deadline v r signature)
  else
    .error .overflow

@[pf_entry]
def approve (s : State) (spender : Address) (amount : UInt256) :
    Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.paused)
  else if Address.isZero spender then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.zeroAddress)
  else if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := Fungible.Allowances.approve storage.allowances Context.caller spender amount,
           paused := s.paused, cap := s.cap, supply := s.supply },
      Event.approval Context.caller spender amount)
  else
    .error .overflow

@[pf_entry]
def increaseAllowance (s : State) (spender : Address) (added : UInt256) :
    Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.paused)
  else if Address.isZero spender then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.zeroAddress)
  else if Fungible.Allowances.canIncrease storage.allowances Context.caller spender added then
    let next := Fungible.Allowances.nextIncrease storage.allowances Context.caller spender added
    .ok ({ dummy := Fungible.Allowances.increase storage.allowances Context.caller spender added,
           paused := s.paused, cap := s.cap, supply := s.supply },
      Event.approval Context.caller spender next)
  else
    .error .overflow

@[pf_entry]
def decreaseAllowance (s : State) (spender : Address) (subtracted : UInt256) :
    Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.paused)
  else if Address.isZero spender then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.zeroAddress)
  else if Fungible.Allowances.canDecrease storage.allowances Context.caller spender subtracted then
    let next := Fungible.Allowances.nextDecrease storage.allowances Context.caller spender subtracted
    .ok ({ dummy := Fungible.Allowances.decrease storage.allowances Context.caller spender subtracted,
           paused := s.paused, cap := s.cap, supply := s.supply },
      Event.approval Context.caller spender next)
  else
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Fungible.Allowances.insufficient storage.allowances Context.caller spender subtracted)

@[pf_entry]
def burn (s : State) (amount : UInt256) : Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.paused)
  else if Fungible.Balances.canDebit storage.balances Context.caller amount then
    let debit := Fungible.Balances.debit storage.balances Context.caller amount
    .ok ({ dummy := debit, paused := s.paused, cap := s.cap,
           supply := UInt256.sub s.supply amount },
      Event.transfer Context.caller Address.zero amount)
  else
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Fungible.Balances.insufficient storage.balances Context.caller amount)

@[pf_entry]
def burnFrom (s : State) (owner : Address) (amount : UInt256) :
    Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.paused)
  else if Address.isZero owner then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.zeroAddress)
  else if Fungible.Allowances.canSpend storage.allowances owner Context.caller amount then
    if Fungible.Balances.canDebit storage.balances owner amount then
      let debit :=
        (Fungible.Balances.debit storage.balances owner amount) |||
        (Fungible.Allowances.spend storage.allowances owner Context.caller amount)
      .ok ({ dummy := debit, paused := s.paused, cap := s.cap,
             supply := UInt256.sub s.supply amount },
        Event.transfer owner Address.zero amount)
    else
      .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
        Fungible.Balances.insufficient storage.balances owner amount)
  else
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Fungible.Allowances.insufficient storage.allowances owner Context.caller amount)

@[pf_entry]
def transfer (s : State) (destination : Address) (amount : UInt256) :
    Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.paused)
  else if Address.isZero destination then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.zeroAddress)
  else if Fungible.Balances.canDebit storage.balances Context.caller amount then
    if Address.eq Context.caller destination ||
        Fungible.Balances.canCredit storage.balances destination amount then
      let movement :=
        Fungible.Balances.transfer storage.balances Context.caller destination amount
      .ok ({ dummy := movement, paused := s.paused, cap := s.cap, supply := s.supply },
        Event.transfer Context.caller destination amount)
    else
      .error .overflow
  else
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Fungible.Balances.insufficient storage.balances Context.caller amount)

@[pf_entry]
def transferFrom (s : State) (owner destination : Address) (amount : UInt256) :
    Except Error (State × UInt64) :=
  if s.paused != 0 then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.paused)
  else if Address.isZero destination then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.zeroAddress)
  else if Fungible.Allowances.canSpend storage.allowances owner Context.caller amount then
    if Fungible.Balances.canDebit storage.balances owner amount then
      if Address.eq owner destination ||
          Fungible.Balances.canCredit storage.balances destination amount then
        let movement :=
          (Fungible.Balances.transfer storage.balances owner destination amount) |||
          (Fungible.Allowances.spend storage.allowances owner Context.caller amount)
        .ok ({ dummy := movement, paused := s.paused, cap := s.cap, supply := s.supply },
          Event.transfer owner destination amount)
      else
        .error .overflow
    else
      .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
        Fungible.Balances.insufficient storage.balances owner amount)
  else
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Fungible.Allowances.insufficient storage.allowances owner Context.caller amount)

@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    if (0 : UInt64) ≠ 1 then
      .ok ({ dummy := s.dummy, paused := 1, cap := s.cap, supply := s.supply }, 1)
    else
      .error .overflow
  else
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.unauthorized Context.caller)

@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    if (0 : UInt64) ≠ 1 then
      .ok ({ dummy := s.dummy, paused := 0, cap := s.cap, supply := s.supply }, 0)
    else
      .error .overflow
  else
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.unauthorized Context.caller)

@[pf_entry]
def pausedOf (s : State) : UInt8 :=
  s.paused

@[pf_entry]
def ownerOf (_s : State) : Address :=
  Immutable.address

@[pf_entry]
def logXfer (s : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Event.transferU64 amount)
  else
    .error .overflow

@[pf_entry]
def logApprove (s : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := s.dummy, paused := s.paused, cap := s.cap, supply := s.supply },
      Event.approvalU64 amount)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Token
