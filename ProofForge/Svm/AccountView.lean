import ProofForge.Core.Ops
import ProofForge.Svm.AccountStorage

namespace ProofForge.Svm.AccountView

/-- The final byte of a selected u64 word must fit in a u64 `data_len`. Same numeric ceiling as
`AccountStorage.maxDataWord`; kept local because the view reads headers, not owned regions. -/
def maxDataWord : Nat := 2305843009213693951

/--
Compile-time bounded remaining-account view. The view owns only two static scalars: physical
accounts `[base, base + capacity)` are addressable by one runtime zero-based `index`, and physical
account 0 stays reserved for authenticated ProofForge state. No runtime geometry, pointer, heap
container, or account copy is represented by this descriptor.
-/
structure View where
  base : Nat
  capacity : Nat
  deriving BEq, Repr, Inhabited

/-- The window must sit inside the external-account region and inside the transaction account-lock
limit. Presence of each account in the window is a runtime property and is checked against
`NUM_ACCOUNTS` at every access, so well-formedness does not force the whole window to exist. -/
def View.wellFormed (view : View) (accountLimit : Nat := 64) : Bool :=
  view.base ≥ 1 && view.capacity > 0 && view.base + view.capacity ≤ accountLimit

/-- Read-only header metadata addressable through a view. -/
inductive Header where
  | lamports
  | dataLen
  | isSigner
  | isWritable
  | key (word : Nat)
  deriving BEq, Repr, Inhabited

/-- A 32-byte public key exposes exactly four little-endian words. -/
def maxKeyWord : Nat := 3

def Header.wellFormed : Header → Bool
  | .key word => word ≤ maxKeyWord
  | _ => true

def Header.canonical : Header → String
  | .lamports => "lp"
  | .dataLen => "dl"
  | .isSigner => "sg"
  | .isWritable => "wr"
  | .key word => s!"k{word}"

/--
Runtime-safe account selection through the existing walk seam. Every query takes one dynamic
zero-based `index`; the target validates `index < capacity` (compile-time bound), then
`base + index < NUM_ACCOUNTS` (available accounts), then walks the account headers in place.
Any failure exits `Custom(1)` before selected field/data bytes are read. There is no write through
a view: persistent state remains fixed account bytes owned by the storage components.
-/
inductive Query where
  | header (view : View) (field : Header)
  | ownerIsSelf (view : View)
  | dataWord (view : View) (word : Nat)
  deriving BEq, Repr, Inhabited

def Query.view : Query → View
  | .header view _ | .ownerIsSelf view | .dataWord view _ => view

def Query.arity : Query → Nat := fun _ => 1

def Query.effects (query : Query) : AccountStorage.EffectSummary :=
  let view := query.view
  { reads := (List.range view.capacity).toArray.map (· + view.base) }

/-- At least the first viewable account must be statically present; the remaining window is
validated at runtime against `NUM_ACCOUNTS`. -/
def Query.minAccounts (measure : V → Nat) (operands : Array V) (query : Query) : Nat :=
  let fromWindow := query.view.base + 1
  operands.foldl (init := fromWindow) fun current value => Nat.max current (measure value)

def Query.wellFormed (query : Query) (accountLimit : Nat := 64) : Bool :=
  let viewOk := query.view.wellFormed accountLimit
  match query with
  | .header _ field => viewOk && field.wellFormed
  | .ownerIsSelf _ => viewOk
  | .dataWord _ word => viewOk && word < maxDataWord

/-- The view never writes and never uses the static walked-header frame; selection re-walks the
bounded account list at access time. -/
def Query.needsWalk (_query : Query) : Bool := true

def Query.canonical (renderValue : V → String) (operands : Array V) (query : Query) : String :=
  let view := query.view
  let tail := s!"({String.intercalate "," (operands.map renderValue).toList})"
  match query with
  | .header _ field => s!"avh.{view.base}.{view.capacity}.{Header.canonical field}{tail}"
  | .ownerIsSelf _ => s!"avo.{view.base}.{view.capacity}{tail}"
  | .dataWord _ word => s!"avd.{view.base}.{view.capacity}.{word}{tail}"

end ProofForge.Svm.AccountView
