/-!
# Bounded Token-2022 TLV account-data policy

This target-local contract owns the account-data preflight for Token-2022 `TransferChecked` CPI
metas. It replaces exact-length equality with one typed plan plus one sole interpreter for a
forward-only bounded TLV cursor over the official Solana state-with-extensions layout. The host
`View` supplies bytes only to state the reference semantics; target plans and cursor states use
fixed scalars, including one UInt64 duplicate bitmap. Generated sBPF has no heap `Array`/`List`/
`Map` payload, no pointer persisted to an account, and no runtime-selected geometry.

## Official pinned layout (evidence, not inferred from comments)

Pinned by `runtime-tests/solana/Cargo.lock`:

- `spl-token-2022-interface-3.1.1/src/extension/mod.rs`
  - `BASE_ACCOUNT_LENGTH = Account::LEN` (165), `BASE_ACCOUNT_AND_TYPE_LENGTH = 166`.
  - `type_and_tlv_indices`: `account_type_index = BASE_ACCOUNT_LENGTH - S::SIZE_OF`; the padding
    bytes `rest[..account_type_index]` must all be zero; the one-byte `AccountType` marker follows;
    the TLV region starts one byte later. For both `Mint` (`SIZE_OF = 82`) and `Account`
    (`SIZE_OF = 165`) the type byte therefore sits at absolute offset 165 and the TLV region at
    absolute offset 166; a mint must additionally zero `data[82..165)`.
  - `unpack_tlv_data` / `StateWithExtensions::unpack`: `check_min_len_and_not_multisig` rejects
    `Multisig::LEN` (355) and anything below the base span; the `AccountType` byte must equal
    `S::ACCOUNT_TYPE` (`Uninitialized = 0`, `Mint = 1`, `Account = 2`).
  - `try_for_each_tlv_extension_type`: the walk ends OK when fewer than two bytes remain, when the
    next `ExtensionType` is `Uninitialized` (0), or at the region end; it rejects
    `InvalidAccountData` when a length is missing or a value overruns the data.
  - TLV entry: `type` = `ExtensionType` (`u16`), `length` = `Length` (`U16`), then the value;
    `get_tlv_indices` fixes `length_start = type_start + 2`, `value_start = type_start + 4`.
  - `ExtensionType` is `#[repr(u16)]` with sequential ordinals `Uninitialized = 0` through
    `PermissionedBurn = 28`; `get_account_type` partitions them into mint-only and account-only.
- `spl-token-interface-2.0.0/src/state.rs`: `Mint::LEN = 82`, `Account::LEN = 165`,
  `Multisig::LEN = 355`.
- `solana-zero-copy-1.2.0/src/unaligned.rs`: `U16` converts through `to_le_bytes`/`from_le_bytes`,
  so TLV headers are little-endian.

## Policy

`closedAccept?` accepts no extension in this slice: only the classic base state (or an
extension-form account whose TLV region holds only official end/padding forms) proceeds to CPI.
Every non-end entry is rejected atomically with a classified reason — `unsupported` for official
`ExtensionType` ordinals whose complete semantics, accounts, and CPI behavior this slice does not
model (transfer-fee, transfer-hook, and all others), `unknown` for ordinals outside the official
set. Harmless-looking extensions stay fail-closed until their full official semantics are proven.
-/

namespace ProofForge.Svm.Cpi.TokenTlv

/-! ## Official pinned layout constants -/

/-- `Multisig::LEN` (spl-token-interface `state.rs`); ambiguous with extensions, rejected. -/
def multisigLen : Nat := 355

/-- `Account::LEN` = `BASE_ACCOUNT_LENGTH` (spl-token-interface `state.rs`). -/
def accountBaseLen : Nat := 165

/-- `Mint::LEN` (spl-token-interface `state.rs`). -/
def mintBaseLen : Nat := 82

/-- Absolute offset of the one-byte `AccountType` marker. -/
def typeByteOffset : Nat := 165

/-- `BASE_ACCOUNT_AND_TYPE_LENGTH`: first absolute offset of the TLV region. -/
def tlvStart : Nat := 166

/-- Zero padding a mint must carry between its 82-byte base and the type byte. -/
def mintPaddingBytes : Nat := 83

/-- `size_of::<ExtensionType>() + size_of::<Length>()`: one little-endian `u16` pair. -/
def headerBytes : Nat := 4

/-- `AccountType::Uninitialized` = `ExtensionType::Uninitialized` (ordinal 0). -/
def uninitializedType : UInt64 := 0

/-- `AccountType::Mint`. -/
def mintTypeByte : Nat := 1

/-- `AccountType::Account`. -/
def accountTypeByte : Nat := 2

/-- Highest official `ExtensionType` ordinal in the pinned interface (`PermissionedBurn = 28`). -/
def knownExtensionMax : Nat := 28

/-! ## Verdicts -/

inductive Reason where
  /-- `Multisig::LEN` is ambiguous with an extension-bearing layout. -/
  | multisigLength
  | tooShort
  /-- A mint's base-to-type-byte padding must be zero. -/
  | paddingNotZero
  /-- The `AccountType` byte must match the constrained base state. -/
  | accountTypeMismatch
  /-- Fewer header bytes remain than the entry requires (or an inconsistent view). -/
  | truncatedHeader
  /-- An accepted entry's value would run past `data_len`. -/
  | bodyOutOfBounds
  /-- Cursor arithmetic wrapped the sBPF u64 register domain. -/
  | arithmeticOverflow
  /-- An official extension this slice does not model. -/
  | unsupported (t : UInt64)
  /-- An ordinal outside the official `ExtensionType` set. -/
  | unknown (t : UInt64)
  /-- A repeated entry of a type the policy would otherwise accept. -/
  | duplicate (t : UInt64)
  /-- More accepted entries than the compile-time `maxHeaders` bound. -/
  | headerCount
  deriving BEq, Repr, Inhabited

inductive Verdict where
  | accept
  | reject (reason : Reason)
  deriving BEq, Repr, Inhabited

/-! ## Official extension classifier -/

inductive ExtensionClass where
  | endMarker
  | known (t : UInt64)
  | unknown (t : UInt64)
  deriving BEq, Repr

/-- Classify one little-endian `u16` extension type against the official pinned set. -/
def classify (t : UInt64) : ExtensionClass :=
  if t == uninitializedType then .endMarker
  else if t ≤ UInt64.ofNat knownExtensionMax then .known t
  else .unknown t

/--
The classifier owning this slice's reject policy: every official extension ordinal whose complete
semantics, account model, and CPI behavior are not modeled here is `unsupported`; anything outside
the official set is `unknown`. Both fail closed.
-/
def rejectReason (t : UInt64) : Reason :=
  match classify t with
  | .known _ => .unsupported t
  | _ => .unknown t

/-! ## Closed source policy vocabulary -/

/-- Which official base state a policy constrains. -/
inductive BaseKind where
  | mint
  | account
  deriving BEq, DecidableEq, Repr, Inhabited

/--
Closed source-facing CPI account-data policy. Source code names a policy; the target plan and its
sole interpreter own its complete meaning. Nothing here exposes raw byte-offset reads.
-/
inductive Policy where
  /--
  Official Token-2022 state-with-extensions slice for `TransferChecked`: the classic base layout
  proceeds; every TLV extension entry rejects atomically before CPI.
  -/
  | token2022Base (kind : BaseKind)
  deriving BEq, DecidableEq, Repr, Inhabited

/-! ## Typed target plan -/

/-- Compile-time plan for one account's TLV policy. Scalars only. -/
structure Plan where
  kind : BaseKind
  baseLen : Nat
  paddingBytes : Nat
  typeByte : Nat
  maxHeaders : Nat
  deriving BEq, Repr, Inhabited

/--
Compile-time TLV entry bound for the bounded cursor. The pinned interface has 28 non-end
ordinals, so one UInt64 bitmap can represent every possible accepted type without allocation.
-/
def defaultMaxHeaders : Nat := knownExtensionMax

def mintPlan : Plan :=
  { kind := .mint, baseLen := mintBaseLen, paddingBytes := mintPaddingBytes,
    typeByte := mintTypeByte, maxHeaders := defaultMaxHeaders }

def accountPlan : Plan :=
  { kind := .account, baseLen := accountBaseLen, paddingBytes := 0,
    typeByte := accountTypeByte, maxHeaders := defaultMaxHeaders }

/-- One plan per closed policy; the interpreter owns the meaning, source code cannot invent one. -/
def planFor : Policy → Except String Plan
  | .token2022Base .mint => .ok mintPlan
  | .token2022Base .account => .ok accountPlan

def Plan.wellFormed (plan : Plan) : Bool :=
  plan.baseLen + plan.paddingBytes + 1 == tlvStart &&
    plan.baseLen + plan.paddingBytes == typeByteOffset &&
    0 < plan.maxHeaders && plan.maxHeaders ≤ knownExtensionMax &&
    match plan.kind with
    | .mint =>
        plan.baseLen == mintBaseLen && plan.paddingBytes == mintPaddingBytes &&
          plan.typeByte == mintTypeByte
    | .account =>
        plan.baseLen == accountBaseLen && plan.paddingBytes == 0 &&
          plan.typeByte == accountTypeByte

/-! ## Bounded TLV cursor -/

/--
Abstract bounded view of one account's data. `readByte offset` is `none` exactly when
`offset ≥ dataLen`; the interpreter never reads past `dataLen` and treats an inconsistent view as
truncated. Host-side gates instantiate it with byte arrays; the emitted machine reads the live
account input through the fixed account header (data length at +80, data at +88).
-/
structure View where
  dataLen : UInt64
  readByte : UInt64 → Option UInt8

/-- Wrap-checked addition over the sBPF u64 register domain: `none` on wraparound. -/
def addBounded (a b : UInt64) : Option UInt64 :=
  let sum := a + b
  if sum < a then none else some sum

/-- One little-endian `u16` TLV header word (type or length). -/
def readU16 (view : View) (offset : UInt64) : Option UInt64 :=
  match addBounded offset 1 with
  | none => none
  | some next =>
    match view.readByte offset, view.readByte next with
    | some lo, some hi => some (UInt64.ofNat hi.toNat * 256 + UInt64.ofNat lo.toNat)
    | _, _ => none

/--
Cursor state. `cursor ≤ dataLen` is maintained by construction. `count` is bounded by
`maxHeaders`; `seenMask` uses bits 1..28 for the pinned official extension ordinals. Both are
fixed UInt64 register values. The emitted closed specialization accepts no extension, so it does
not need to materialize either value yet.
-/
structure State where
  cursor : UInt64
  count : UInt64
  seenMask : UInt64
  deriving Repr, Inhabited

/-- The cursor starts at the official TLV region start. -/
def initialState : State :=
  { cursor := UInt64.ofNat tlvStart, count := 0, seenMask := 0 }

/--
Sole interpreter: one forward-only bounded TLV cursor. Every header read happens only after the
remaining span proves the offsets are inside `data_len`; every accepted body advance proves
`cursor + 4 + length ≤ data_len` through wrap-checked arithmetic and the subtraction-form bound,
rejecting overflow, truncated headers, duplicates, unsupported/unknown entries, and runs exceeding
`maxHeaders`. Fuel bounds recursion; each accepted entry consumes one unit.
-/
def firstEntry (view : View) (offset rem : UInt64) (fallback : UInt64 → Verdict) : Verdict :=
  if rem == 0 ∨ rem == 1 then .accept
  else
    match readU16 view offset with
    | none => .reject .truncatedHeader
    | some t =>
      if rem < 4 then if t == 0 then .accept else .reject .truncatedHeader
      else if t == 0 then .accept else fallback t

def acceptedEntry (plan : Plan) (accept? : UInt64 → Bool) (view : View)
    (recurse : State → Verdict) (st : State) (t : UInt64) : Verdict :=
  if !accept? t then .reject (rejectReason t)
  else if t > UInt64.ofNat knownExtensionMax then .reject (.unknown t)
  else
    match addBounded st.cursor 2 with
    | none => .reject .arithmeticOverflow
    | some lengthOffset =>
      match readU16 view lengthOffset with
      | none => .reject .truncatedHeader
      | some bodyLen =>
        match addBounded st.cursor 4 with
        | none => .reject .arithmeticOverflow
        | some valueStart =>
          if bodyLen > view.dataLen - valueStart then .reject .bodyOutOfBounds
          else
            match addBounded valueStart bodyLen with
            | none => .reject .arithmeticOverflow
            | some next =>
              if st.count ≥ UInt64.ofNat plan.maxHeaders then .reject .headerCount
              else
                let bit := (1 : UInt64) <<< t
                if st.seenMask &&& bit != 0 then .reject (.duplicate t)
                else recurse
                  { cursor := next, count := st.count + 1, seenMask := st.seenMask ||| bit }

def run (plan : Plan) (accept? : UInt64 → Bool) (view : View) : Nat → State → Verdict
  | 0, _ => .reject .headerCount
  | fuel + 1, st =>
    let len := view.dataLen
    if len < st.cursor then .reject .truncatedHeader
    else
      let rem := len - st.cursor
      firstEntry view st.cursor rem
        (acceptedEntry plan accept? view (run plan accept? view fuel) st)

/--
Padding and `AccountType` checks for the extension form (`data_len ≥ tlvStart`), shared by the
interpreter wrapper and the straight-line mirror.
-/
def extensionFormCheck (plan : Plan) (view : View) : Option Reason :=
  let rec paddingZero (offset remaining : Nat) : Bool :=
    match remaining with
    | 0 => true
    | n + 1 =>
      match view.readByte (UInt64.ofNat offset) with
      | some b => b == 0 && paddingZero (offset + 1) n
      | none => false
  let paddingZero := paddingZero plan.baseLen plan.paddingBytes
  if !paddingZero then some .paddingNotZero
  else
    match view.readByte (UInt64.ofNat typeByteOffset) with
    | none => some .accountTypeMismatch
    | some b => if b.toNat == plan.typeByte then none else some .accountTypeMismatch

/--
Shared official base-state checks: `Multisig::LEN` ambiguity, base span, mint padding zeros, and
the `AccountType` byte. The classic base length is reported as `none`; the caller accepts it
without running the cursor (there is no TLV region to walk).
-/
def baseCheck (plan : Plan) (view : View) : Option Reason :=
  let len := view.dataLen.toNat
  if len == multisigLen then some .multisigLength
  else if len < plan.baseLen then some .tooShort
  else if len == plan.baseLen then none
  else if len < tlvStart then some .tooShort
  else extensionFormCheck plan view

/--
This slice's closed classifier: no extension type is acceptable. Every non-end entry rejects
atomically with a classified reason.
-/
def closedAccept? (_ : UInt64) : Bool := false

/--
Full policy verdict for one account: official base checks, then the bounded cursor. This is the
single function the emitted preflight realizes.
-/
def evaluate (plan : Plan) (accept? : UInt64 → Bool) (view : View) : Verdict :=
  let len := view.dataLen.toNat
  if len == multisigLen then .reject .multisigLength
  else if len < plan.baseLen then .reject .tooShort
  else if len == plan.baseLen then .accept
  else if len < tlvStart then .reject .tooShort
  else
    match extensionFormCheck plan view with
    | some reason => .reject reason
    | none => run plan accept? view (plan.maxHeaders + 1) initialState

/--
Straight-line mirror of the emitted specialization for a classifier that accepts no extension:
the machine needs no loop, no length read, and no advance because every non-end entry rejects at
its four-byte header. Kept in lockstep with `emitPreflight`.
-/
def straightline (plan : Plan) (view : View) : Verdict :=
  let len := view.dataLen.toNat
  if len == multisigLen then .reject .multisigLength
  else if len < plan.baseLen then .reject .tooShort
  else if len == plan.baseLen then .accept
  else if len < tlvStart then .reject .tooShort
  else
    match extensionFormCheck plan view with
    | some reason => .reject reason
    | none =>
      firstEntry view (UInt64.ofNat tlvStart) (view.dataLen - UInt64.ofNat tlvStart)
        (fun t => .reject (rejectReason t))

/--
The emitted machine is the interpreter's specialization for the closed classifier: with no
acceptable extension, the cursor never advances past the first header, so the straight-line
preflight and the full bounded cursor agree on every view.
-/
theorem evaluate_closed_eq_straightline (plan : Plan) (view : View) :
    evaluate plan closedAccept? view = straightline plan view := by
  simp only [evaluate, straightline]
  split <;> rename_i h1
  · rfl
  · split <;> rename_i h2
    · rfl
    · split <;> rename_i h3
      · rfl
      · split <;> rename_i h4
        · rfl
        · split
          · rfl
          · next hnone =>
            have hmod : tlvStart % 18446744073709551616 = tlvStart :=
              Nat.mod_eq_of_lt (by decide)
            have hnc : ¬ (view.dataLen < UInt64.ofNat tlvStart) := by
              intro hc
              have hc' : view.dataLen.toNat < tlvStart := by
                simpa [hmod] using (UInt64.lt_iff_toNat_lt).mp hc
              omega
            simp only [run, initialState, if_neg hnc]
            rfl

theorem mintPlan_wellFormed : mintPlan.wellFormed := by decide

theorem accountPlan_wellFormed : accountPlan.wellFormed := by decide

theorem planFor_yields_wellFormed : ∀ p, ∃ plan, planFor p = .ok plan ∧ plan.wellFormed := by
  intro p
  cases p with
  | token2022Base kind =>
    cases kind with
    | mint => exact ⟨mintPlan, rfl, mintPlan_wellFormed⟩
    | account => exact ⟨accountPlan, rfl, accountPlan_wellFormed⟩

/-- The classifier partitions every ordinal into the three official shapes. -/
theorem classify_total (t : UInt64) :
    classify t = .endMarker ∨ (∃ t', classify t = .known t') ∨ (∃ t', classify t = .unknown t') := by
  unfold classify
  split
  · exact .inl rfl
  · split
    · exact .inr (.inl ⟨_, rfl⟩)
    · exact .inr (.inr ⟨_, rfl⟩)

end ProofForge.Svm.Cpi.TokenTlv
