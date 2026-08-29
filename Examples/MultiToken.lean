import ProofForge.Evm.Sdk

/-!
Owner-minted bounded ERC-1155 consumer. The SDK owns the token-id key envelope, the
(owner, id) balance and (owner, operator) operator maps, and checked mint/burn/transfer
movement. This contract owns the immutable minter gate, zero-address policy, error ordering
(`Unauthorized`/`ZeroAddress`/`Insufficient`) and event usage (the existing Transfer event carries
the moved amount; token ids and standard ERC-1155 typed events stay unlogged).
-/

namespace Examples.MultiToken

open ProofForge.Evm.Sdk

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def balances : Erc1155.Balances :=
  Storage.Layout.root.addressPairMap256.handle

@[pf_inline] def operators : Erc1155.Operators :=
  Storage.Layout.root.addressPairMap256.next.addressPairMap.handle

@[pf_entry]
def init (_owner : Address) : State :=
  { dummy := 0 }

@[pf_entry]
def mint (s : State) (to : Address) (tokenId : UInt256) (amount : UInt256) :
    Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    if Erc1155.canMint balances to tokenId amount then
      .ok ({ dummy := Erc1155.mint balances to tokenId amount },
        Event.transfer Address.zero to amount)
    else if Address.isZero to then
      .ok (s, Revert.zeroAddress)
    else
      .ok (s, Revert.unauthorized Context.caller)
  else
    .ok (s, Revert.unauthorized Context.caller)

/-- Burn from the caller's own balance. Unencodable ids are `Unauthorized`; an encodable id
whose balance is short is `Insufficient(held, wanted)`. No event: zero-address event operands
stay application-owned (see Badge). -/
@[pf_entry]
def burn (s : State) (tokenId : UInt256) (amount : UInt256) :
    Except Error (State × UInt64) :=
  if Erc1155.canBurn balances Context.caller tokenId amount then
    .ok ({ dummy := Erc1155.burn balances Context.caller tokenId amount }, 0)
  else if !Erc1155.canEncode tokenId then
    .ok (s, Revert.unauthorized Context.caller)
  else
    .ok (s, Erc1155.Balances.insufficient balances Context.caller tokenId amount)

@[pf_entry]
def setApprovalForAll (s : State) (operator : Address) (approved : Bool) :
    Except Error (State × UInt64) :=
  if Address.isZero operator then
    .ok (s, Revert.zeroAddress)
  else if Address.eq operator Context.caller then
    .ok (s, Revert.unauthorized Context.caller)
  else if (0 : UInt64) ≠ 1 then
    -- ApprovalForAll has no ERC-20-shaped Event.approval encoding; logging stays app-owned.
    .ok ({ dummy :=
        Erc1155.Operators.setApprovalForAll operators Context.caller operator approved }, 0)
  else
    .error .overflow

@[pf_entry]
def transferFrom (s : State) (source to : Address) (tokenId : UInt256) (amount : UInt256) :
    Except Error (State × UInt64) :=
  if !Erc1155.isApprovedOrOwner operators Context.caller source tokenId then
    .ok (s, Revert.unauthorized Context.caller)
  else if Address.isZero to then
    .ok (s, Revert.zeroAddress)
  else if Erc1155.Balances.canTransfer balances source to tokenId amount then
    .ok ({ dummy := Erc1155.Balances.transfer balances source to tokenId amount },
      Event.transfer source to amount)
  else
    .ok (s, Erc1155.Balances.insufficient balances source tokenId amount)

/-- Single-id balance view through the SDK-owned checked key-envelope gate. -/
@[pf_entry]
def balanceOf (_s : State) (owner : Address) (tokenId : UInt256) : UInt256 :=
  Erc1155.Balances.balanceOf balances owner tokenId

@[pf_entry]
def isApprovedForAll (_s : State) (owner operator : Address) : Bool :=
  Erc1155.Operators.isApprovedForAll operators owner operator

end Examples.MultiToken
