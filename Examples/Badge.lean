import ProofForge.Evm.Sdk

/-!
Burnable ERC-721 consumer with operator approvals. Independently reuses the Erc721 ledger
handles while owning burn authorization and setApprovalForAll policy.
-/

namespace Examples.Badge

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
def setApprovalForAll (s : State) (operator : Address) (approved : Bool) :
    Except Error (State × UInt64) :=
  if Address.isZero operator then
    .ok (s, Revert.zeroAddress)
  else if Address.eq operator Context.caller then
    .ok (s, Revert.unauthorized Context.caller)
  else if (0 : UInt64) ≠ 1 then
    -- ApprovalForAll has no ERC-20-shaped Event.approval encoding; logging stays app-owned.
    .ok ({ dummy :=
        Erc721.Operators.setApprovalForAll operators Context.caller operator approved }, 0)
  else
    .error .overflow

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

@[pf_entry]
def burn (s : State) (tokenId : UInt256) : Except Error (State × UInt64) :=
  let owner := Erc721.Owners.ownerOf owners tokenId
  if !Erc721.isApprovedOrOwner owners approvals operators Context.caller tokenId then
    .ok (s, Revert.unauthorized Context.caller)
  else if Erc721.canBurn owners balances owner tokenId then
    -- Avoid Event.transfer (... Address.zero ...); Address.zero in effect position has been
    -- mis-lowered before. Burn success returns 0 and leaves Transfer logging to the app.
    .ok ({ dummy := Erc721.burn owners approvals balances owner tokenId }, 0)
  else
    .ok (s, Revert.unauthorized Context.caller)

/-- Packed owner; see Collectible.ownerOf for why this is `UInt256` rather than `Address`.
Unencodable ids return zero (no `tokenKey` alias). -/
@[pf_entry]
def ownerOf (_s : State) (tokenId : UInt256) : UInt256 :=
  if !Erc721.canEncode tokenId then UInt256.zero
  else owners.get (Erc721.tokenKey tokenId)

/-- Packed per-token approval. -/
@[pf_entry]
def getApproved (_s : State) (tokenId : UInt256) : UInt256 :=
  if !Erc721.canEncode tokenId then UInt256.zero
  else approvals.get (Erc721.tokenKey tokenId)

@[pf_entry]
def isApprovedForAll (_s : State) (owner operator : Address) : Bool :=
  Erc721.Operators.isApprovedForAll operators owner operator

@[pf_entry]
def balanceOf (_s : State) (owner : Address) : UInt256 :=
  Erc721.Balances.balanceOf256 balances owner

end Examples.Badge
