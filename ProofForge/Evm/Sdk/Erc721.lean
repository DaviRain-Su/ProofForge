import ProofForge.Evm.Sdk.Base

namespace ProofForge.Evm.Sdk.Erc721

/-!
# EVM SDK ERC-721 core (EVM-SDK-7a)

Reusable O(1) ownership, per-token approval, operator approval, and balance movement over the
existing hashed-map namespaces. Token ids are `UInt256` values whose top limb is zero so the id
fits an `Address` map key (`tokenKey`). Owner and approved addresses are packed into `UInt256`
values with a zero top limb. Per-owner balances use a UInt64 address map (NFT counts stay far
below 2^64). Authorization against `Context.caller`, pause/zero-address policy, mint caps,
receiver hooks, and events remain application-owned.

There is no new Runtime leaf, hashed-map kind, Op/IR/Emit recipe, or ERC-721 LOG4 topic. Consumers
may reuse `Event.transfer` / `Event.approval` with the token id in the amount limb, or keep logging
application-local.
-/

/-- UInt256 unit used only for application event amount limbs. -/
@[pf_inline] def one : UInt256 := ⟨1, 0, 0, 0⟩

/-- True when `tokenId` fits the three-limb `Address` map key (top UInt256 limb is zero). -/
@[pf_inline] def canEncode (tokenId : UInt256) : Bool :=
  tokenId.w3 == 0

/-- Map key for one token id. Precondition: `canEncode tokenId`. -/
@[pf_inline] def tokenKey (tokenId : UInt256) : Address :=
  ⟨tokenId.w0, tokenId.w1, tokenId.w2⟩

@[pf_inline] def packAddress (address : Address) : UInt256 :=
  ⟨address.w0, address.w1, address.w2, 0⟩

@[pf_inline] def unpackAddress (value : UInt256) : Address :=
  ⟨value.w0, value.w1, value.w2⟩

/-- Compile-time handle to tokenId → owner storage. -/
abbrev Owners := Storage.AddressMap256

/-- Compile-time handle to tokenId → approved spender storage. -/
abbrev TokenApprovals := Storage.AddressMap256

/-- Compile-time handle to (owner, operator) → UInt64 approval flag storage. -/
abbrev Operators := Storage.AddressPairMap

/-- Per-owner token counts as UInt64 (hashed address map). -/
abbrev Balances := Storage.AddressMap

namespace Owners

/-- Owner of `tokenId`. Precondition for a meaningful result: `canEncode tokenId`
(otherwise `tokenKey` truncates and may alias another id). -/
@[pf_inline] def ownerOf (owners : Owners) (tokenId : UInt256) : Address :=
  unpackAddress (owners.get (tokenKey tokenId))

@[pf_inline] def isMinted (owners : Owners) (tokenId : UInt256) : Bool :=
  !Address.isZero (owners.ownerOf tokenId)

@[pf_inline] def putOwner (owners : Owners) (tokenId : UInt256) (owner : Address) : UInt64 :=
  owners.put (tokenKey tokenId) (packAddress owner)

@[pf_inline] def clear (owners : Owners) (tokenId : UInt256) : UInt64 :=
  owners.put (tokenKey tokenId) UInt256.zero

end Owners

namespace TokenApprovals

/-- Approved spender for `tokenId`. Precondition for a meaningful result: `canEncode tokenId`. -/
@[pf_inline] def getApproved (approvals : TokenApprovals) (tokenId : UInt256) : Address :=
  unpackAddress (approvals.get (tokenKey tokenId))

@[pf_inline] def approve (approvals : TokenApprovals) (tokenId : UInt256)
    (spender : Address) : UInt64 :=
  approvals.put (tokenKey tokenId) (packAddress spender)

@[pf_inline] def clear (approvals : TokenApprovals) (tokenId : UInt256) : UInt64 :=
  approvals.put (tokenKey tokenId) UInt256.zero

end TokenApprovals

namespace Operators

@[pf_inline] def isApprovedForAll (operators : Operators)
    (owner operator : Address) : Bool :=
  operators.get owner operator != 0

@[pf_inline] def setApprovalForAll (operators : Operators)
    (owner operator : Address) (approved : Bool) : UInt64 :=
  operators.put owner operator (if approved then (1 : UInt64) else 0)

end Operators

namespace Balances

@[pf_inline] def balanceOf (balances : Balances) (owner : Address) : UInt64 :=
  balances.get owner

/-- ABI-facing UInt256 view of the UInt64 count. -/
@[pf_inline] def balanceOf256 (balances : Balances) (owner : Address) : UInt256 :=
  ⟨balances.get owner, 0, 0, 0⟩

@[pf_inline] def canCredit (balances : Balances) (owner : Address) : Bool :=
  balances.get owner != ~~~(0 : UInt64)

@[pf_inline] def credit (balances : Balances) (owner : Address) : UInt64 :=
  balances.put owner (balances.get owner + 1)

@[pf_inline] def canDebit (balances : Balances) (owner : Address) : Bool :=
  balances.get owner != 0

@[pf_inline] def debit (balances : Balances) (owner : Address) : UInt64 :=
  balances.put owner (balances.get owner - 1)

end Balances

/-- True when `spender` is the owner, the per-token approved address, or an approved operator.
Unencodable token ids are never authorized (same gate as mutation predicates). -/
@[pf_inline] def isApprovedOrOwner (owners : Owners) (approvals : TokenApprovals)
    (operators : Operators) (spender : Address) (tokenId : UInt256) : Bool :=
  canEncode tokenId &&
    (let owner := owners.ownerOf tokenId
     Address.eq spender owner ||
       Address.eq spender (approvals.getApproved tokenId) ||
       operators.isApprovedForAll owner spender)

/-- Mint is valid when the id encodes, the token is absent, the recipient is nonzero, and the
recipient balance can accept one more token. -/
@[pf_inline] def canMint (owners : Owners) (balances : Balances)
    (to : Address) (tokenId : UInt256) : Bool :=
  canEncode tokenId &&
    !owners.isMinted tokenId &&
    !Address.isZero to &&
    balances.canCredit to

/-- Persist ownership and credit the recipient balance by one. Precondition:
`canMint owners balances to tokenId`. -/
@[pf_inline] def mint (owners : Owners) (balances : Balances)
    (to : Address) (tokenId : UInt256) : UInt64 :=
  owners.putOwner tokenId to ||| balances.credit to

/-- Burn is valid when the id encodes and is owned by `source`. -/
@[pf_inline] def canBurn (owners : Owners) (balances : Balances)
    (source : Address) (tokenId : UInt256) : Bool :=
  canEncode tokenId &&
    Address.eq (owners.ownerOf tokenId) source &&
    balances.canDebit source

/-- Clear approval and ownership after debiting the owner balance. Precondition:
`canBurn owners balances source tokenId`. Debit runs first so the owner address is still
readable if Extract re-inlines `owners.ownerOf` into the balance key. -/
@[pf_inline] def burn (owners : Owners) (approvals : TokenApprovals) (balances : Balances)
    (source : Address) (tokenId : UInt256) : UInt64 :=
  balances.debit source |||
    approvals.clear tokenId |||
    owners.clear tokenId

/-- Transfer is valid when the id encodes, `source` owns it, `to` is nonzero, and balances cover a
one-token move (same-address transfers only need the ownership gate). -/
@[pf_inline] def canTransfer (owners : Owners) (balances : Balances)
    (source to : Address) (tokenId : UInt256) : Bool :=
  canEncode tokenId &&
    Address.eq (owners.ownerOf tokenId) source &&
    !Address.isZero to &&
    (Address.eq source to ||
      (balances.canDebit source && balances.canCredit to))

/-- Move ownership, clear the per-token approval, and adjust balances. Equal `source`/`to` only
clears approval. Precondition: `canTransfer owners balances source to tokenId`. -/
@[pf_inline] def transfer (owners : Owners) (approvals : TokenApprovals) (balances : Balances)
    (source to : Address) (tokenId : UInt256) : UInt64 :=
  if Address.eq source to then
    approvals.clear tokenId
  else
    approvals.clear tokenId |||
      owners.putOwner tokenId to |||
      balances.debit source |||
      balances.credit to

end ProofForge.Evm.Sdk.Erc721
