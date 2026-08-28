import ProofForge.Attr
import ProofForge.Evm.Sdk.Base

namespace ProofForge.Evm.Sdk.Roles

/-!
# EVM SDK bounded static role sets

`Set2` is a fixed-capacity role policy over two explicit `Address` slots;
`Address.zero` denotes a vacancy. It owns membership and slot-selection decisions, while
applications own authorization, error policy, and literal state-field updates. This keeps all
storage writes visible and adds no map namespace, runtime layout object, or allocator.

Consumers store two adjacent Address fields, reconstruct `Set2` for decisions, and mirror those
fields in `Storage.Static`. Duplicate grants and nonmember revokes are idempotent; zero is never a
member; a third distinct grant is full.

The pattern matches in these helpers are part of the current compiler-erased contract: they expose
the consumer's field expressions to Address limb lowering. Dynamic indexed Address reads are not
published until their zero/OOB return path is supported by extraction.
-/

/-- Compile-time capacity of one role set. -/
@[pf_inline] def capacity : Nat := 2

/-- Two explicit role slots; `Address.zero` marks a vacancy. -/
structure Set2 where
  /-- Slot `0`: first member when nonzero, vacant when zero. -/
  slot0 : Address
  /-- Slot `1`: second member when nonzero, vacant when zero. -/
  slot1 : Address
  deriving Repr, DecidableEq, Inhabited

attribute [pf_inline] Set2.slot0 Set2.slot1

namespace Set2

/-- The empty role set: both slots vacant. -/
@[pf_inline] def empty : Set2 :=
  ⟨Address.zero, Address.zero⟩

/-- Membership decision: `who` occupies a nonzero slot. The zero address is never a member. -/
@[pf_inline] def member (rs : Set2) (who : Address) : Bool :=
  match rs with
  | ⟨a, b⟩ => (!Address.isZero a && Address.eq a who) || (!Address.isZero b && Address.eq b who)

/-- Vacancy decision: at least one slot is free. -/
@[pf_inline] def hasVacancy (rs : Set2) : Bool :=
  match rs with
  | ⟨a, b⟩ => Address.isZero a || Address.isZero b

/-- Full decision: no slot is free; a grant of a nonmember selects `CapExceeded()`. -/
@[pf_inline] def full (rs : Set2) : Bool :=
  !hasVacancy rs

/-- Whether `who` is a new nonzero member and a slot is available. -/
@[pf_inline] def canGrant (rs : Set2) (who : Address) : Bool :=
  !Address.isZero who && !member rs who && hasVacancy rs

/-- Whether an admissible grant should fill the first explicit state field. -/
@[pf_inline] def grantSlot0 (rs : Set2) (who : Address) : Bool :=
  match rs with
  | ⟨a, _b⟩ => canGrant rs who && Address.isZero a

/-- Whether an admissible grant should fill the second explicit state field. -/
@[pf_inline] def grantSlot1 (rs : Set2) (who : Address) : Bool :=
  match rs with
  | ⟨a, b⟩ => canGrant rs who && !Address.isZero a && Address.isZero b

/-- Whether revoking `who` should clear the first explicit state field. -/
@[pf_inline] def revokeSlot0 (rs : Set2) (who : Address) : Bool :=
  match rs with
  | ⟨a, _b⟩ => !Address.isZero a && Address.eq a who

/-- Whether revoking `who` should clear the second explicit state field. -/
@[pf_inline] def revokeSlot1 (rs : Set2) (who : Address) : Bool :=
  match rs with
  | ⟨_a, b⟩ => !Address.isZero b && Address.eq b who

end Set2

end ProofForge.Evm.Sdk.Roles
