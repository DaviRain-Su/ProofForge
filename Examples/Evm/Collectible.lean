import ProofForge.Evm.Sdk

/-!
Owner-minted ERC-721 consumer. The SDK owns token-id encoding, ownership/approval maps, and
checked mint/transfer movement. This contract owns the immutable minter gate, zero-address
policy, and event ordering (token id carried in the existing transfer/approval amount limb).
-/

namespace Examples.Evm.Collectible
open ProofForge.Evm.Sdk

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def owners : Erc721.Owners :=
  Storage.Layout.root.addressMap256.handle

@[pf_inline] def approvals : Erc721.TokenApprovals :=
  Storage.Layout.root.addressMap256.next.addressMap256.handle

@[pf_inline] def operators : Erc721.Operators :=
  Storage.Layout.root.addressMap256.next.addressMap256.next.addressPairMap.handle

@[pf_inline] def balances : Erc721.Balances :=
  Storage.Layout.root.addressMap256.next.addressMap256.next.addressPairMap.next
    |>.addressMap.handle

@[pf_entry]
def init (_owner : Address) : State :=
  { dummy := 0 }

@[pf_entry]
def mint (s : State) (to : Address) (tokenId : UInt256) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    if Erc721.canMint owners balances to tokenId then
      .ok ({ dummy := Erc721.mint owners balances to tokenId },
        Event.transfer Address.zero to tokenId)
    else if Address.isZero to then
      .ok (s, Revert.zeroAddress)
    else
      .ok (s, Revert.unauthorized Context.caller)
  else
    .ok (s, Revert.unauthorized Context.caller)

@[pf_entry]
def approve (s : State) (spender : Address) (tokenId : UInt256) :
    Except Error (State × UInt64) :=
  if !Erc721.canEncode tokenId then
    .ok (s, Revert.unauthorized Context.caller)
  else if Address.eq (Erc721.Owners.ownerOf owners tokenId) Context.caller then
    .ok ({ dummy := Erc721.TokenApprovals.approve approvals tokenId spender },
      Event.approval Context.caller spender tokenId)
  else
    .ok (s, Revert.unauthorized Context.caller)

@[pf_entry]
def transferFrom (s : State) (source to : Address) (tokenId : UInt256) :
    Except Error (State × UInt64) :=
  if !Erc721.isApprovedOrOwner owners approvals operators Context.caller tokenId then
    .ok (s, Revert.unauthorized Context.caller)
  else if Address.isZero to then
    .ok (s, Revert.zeroAddress)
  else if Erc721.canTransfer owners balances source to tokenId then
    .ok ({ dummy := Erc721.transfer owners approvals balances source to tokenId },
      Event.transfer source to tokenId)
  else
    .ok (s, Revert.unauthorized Context.caller)

/-- Packed owner (`⟨w0,w1,w2,0⟩`). Address-typed returns from map reads still expand to four
UInt256 limbs under Extract, so consumers expose the packed word until Emit grows a 3-limb
Address path for hashed-map loads. Unencodable ids return zero (no `tokenKey` alias). -/
@[pf_entry]
def ownerOf (_s : State) (tokenId : UInt256) : UInt256 :=
  if !Erc721.canEncode tokenId then UInt256.zero
  else owners.get (Erc721.tokenKey tokenId)

/-- Packed per-token approval; same Extract limitation as `ownerOf`. -/
@[pf_entry]
def getApproved (_s : State) (tokenId : UInt256) : UInt256 :=
  if !Erc721.canEncode tokenId then UInt256.zero
  else approvals.get (Erc721.tokenKey tokenId)

@[pf_entry]
def balanceOf (_s : State) (owner : Address) : UInt256 :=
  Erc721.Balances.balanceOf256 balances owner

end Examples.Evm.Collectible