import ProofForge.Attr
import ProofForge.Svm.Memory
import ProofForge.Svm.Sdk.Account
import ProofForge.Svm.Sdk.Pubkey

/-!
# Bounded Instructions / fixed-offset sliced sysvar

Compile-time fixed windows over a named sysvar account (svm-rt-004). Extraction erases the
descriptors to existing `accDataLen` / `accDataWord` / key-word queries. This is not
`sol_get_sysvar` and does not admit arbitrary runtime blob geometry.

Length arguments that appear in extracted comparisons must be call-site `Nat` constants (or
top-level `def` aliases), not structure-field projections — the extractor does not reduce
`ix.serializedBytes` inside `UInt64.ofNat`.

Lives outside `Sdk.Sysvar` so Clock/Epoch/Rent stay free of the Account ↔ Sysvar import cycle.
-/

namespace ProofForge.Svm.Sdk.Sysvar

open ProofForge.Svm.Sdk

/-- Official Instructions sysvar id: `Sysvar1nstructions1111111111111111111111111`. -/
@[pf_inline] def instructionsKey : Pubkey :=
  Pubkey.ofWords 7408838205410486022 13889942742359136821
    11922530290679293121 35966925531

/--
Compile-time fixed byte window into one account's data. Geometry is static; extraction erases the
descriptor. Short accounts fail closed at the source without opening a generic runtime slice API.
-/
structure Slice where
  account : Account.Handle
  offsetBytes : Nat
  lengthBytes : Nat
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Slice.account Slice.offsetBytes Slice.lengthBytes

@[pf_inline] def Slice.accountData
    (account : Account.Handle) (offsetBytes lengthBytes : Nat) : Slice :=
  { account, offsetBytes, lengthBytes }

def Slice.endOffset (slice : Slice) : Nat :=
  slice.offsetBytes + slice.lengthBytes

/-- Word-aligned, non-empty, account-bounded window inside the Solana account-data ceiling. -/
def Slice.wellFormed (slice : Slice) (accountLimit : Nat := 64) : Bool :=
  slice.account.wellFormed accountLimit &&
    slice.lengthBytes > 0 &&
    slice.offsetBytes % 8 == 0 &&
    slice.lengthBytes % 8 == 0 &&
    slice.endOffset ≤ ProofForge.Svm.Memory.maxAccountDataBytes

/-- Runtime length gate against an explicit compile-time minimum length (`UInt64` constant). -/
@[pf_inline] def sliceFits (account : Account.Handle) (minLen : UInt64) : Bool :=
  !(account.dataLen < minLen)

/--
Read one little-endian `u64` at a compile-time absolute word index, gated by an explicit minimum
length (`UInt64` constant). Short accounts return `0`.
-/
@[pf_inline] def sliceWord
    (account : Account.Handle) (minLen : UInt64) (word : Nat) : UInt64 :=
  if account.dataLen < minLen then
    0
  else
    account.dataWord word

/-- Convenience: word relative to a compile-time byte offset (must be word-aligned). -/
@[pf_inline] def sliceWordAt
    (account : Account.Handle) (offsetBytes : Nat) (minLen : UInt64) (word : Nat) : UInt64 :=
  sliceWord account minLen (offsetBytes / 8 + word)

@[pf_inline] def Slice.fits (slice : Slice) : Bool :=
  sliceFits slice.account (UInt64.ofNat slice.endOffset)

/-- Prefer `sliceWord` / `sliceWordAt` with explicit constants in extracted entries. -/
def Slice.word (slice : Slice) (word : Nat) : UInt64 :=
  sliceWordAt slice.account slice.offsetBytes (UInt64.ofNat slice.endOffset) word

/--
Bounded Instructions sysvar view. `serializedBytes` is the compile-time total length of the
serialized instruction blob **including** the trailing current-index `u16`.
-/
structure Instructions where
  account : Account.Handle
  serializedBytes : Nat
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Instructions.account Instructions.serializedBytes

@[pf_inline] def Instructions.view
    (account : Account.Handle) (serializedBytes : Nat) : Instructions :=
  { account, serializedBytes }

def Instructions.wellFormed (ix : Instructions) (accountLimit : Nat := 64) : Bool :=
  ix.account.wellFormed accountLimit &&
    ix.serializedBytes ≥ 2 &&
    ix.serializedBytes ≤ ProofForge.Svm.Memory.maxAccountDataBytes

@[pf_inline] def instructionsAuthenticated (account : Account.Handle) : Bool :=
  account.key.equals instructionsKey

@[pf_inline] def instructionsFits (account : Account.Handle) (serializedBytes : UInt64) : Bool :=
  sliceFits account serializedBytes

/-- `num_instructions` as the little-endian `u16` at offset 0. Short → `0`. -/
@[pf_inline] def numInstructionsAt
    (account : Account.Handle) (serializedBytes : UInt64) : UInt64 :=
  if account.dataLen < serializedBytes then
    0
  else
    account.dataWord 0 &&& (0xffff : UInt64)

/--
Current instruction index as a little-endian `u16` packed into account data. Short → `0`.

`word` / `shift` are the compile-time absolute data-word index and bit shift for the trailing
`u16` (for a 24-byte blob at offset 22: word = 2, shift = 48). The extractor needs these as
numerals rather than `serializedBytes - 2` arithmetic in the instruction body.
-/
@[pf_inline] def currentIndexAt
    (account : Account.Handle) (serializedBytes : UInt64) (word shift : Nat) : UInt64 :=
  if account.dataLen < serializedBytes then
    0
  else
    (account.dataWord word >>> UInt64.ofNat shift) &&& (0xffff : UInt64)

@[pf_inline] def Instructions.authenticated (ix : Instructions) : Bool :=
  instructionsAuthenticated ix.account

@[pf_inline] def Instructions.fits (ix : Instructions) : Bool :=
  instructionsFits ix.account (UInt64.ofNat ix.serializedBytes)

def Instructions.numInstructions (ix : Instructions) : UInt64 :=
  numInstructionsAt ix.account (UInt64.ofNat ix.serializedBytes)

/-- Host helper for the common end-u16 layout; extracted entries should call `currentIndexAt`
with explicit word/shift numerals. -/
def Instructions.currentIndex (ix : Instructions) : UInt64 :=
  let off := ix.serializedBytes - 2
  currentIndexAt ix.account (UInt64.ofNat ix.serializedBytes) (off / 8) (8 * (off % 8))

@[pf_inline] def Instructions.slice
    (ix : Instructions) (offsetBytes lengthBytes : Nat) : Slice :=
  Slice.accountData ix.account offsetBytes lengthBytes

/-! ### svm-rt-004：Slice / Instructions L1 几何 -/

theorem Slice.endOffset_def (slice : Slice) :
    slice.endOffset = slice.offsetBytes + slice.lengthBytes := rfl

theorem Slice.wellFormed_account_lt
    (slice : Slice) (accountLimit : Nat) (h : slice.wellFormed accountLimit = true) :
    slice.account.index < accountLimit := by
  simp [Slice.wellFormed, Account.Handle.wellFormed] at h
  exact h.1.1.1.1

theorem Slice.wellFormed_length_pos
    (slice : Slice) (accountLimit : Nat) (h : slice.wellFormed accountLimit = true) :
    0 < slice.lengthBytes := by
  simp [Slice.wellFormed] at h
  exact h.1.1.1.2

theorem Slice.wellFormed_endOffset_le
    (slice : Slice) (accountLimit : Nat) (h : slice.wellFormed accountLimit = true) :
    slice.endOffset ≤ ProofForge.Svm.Memory.maxAccountDataBytes := by
  simp [Slice.wellFormed] at h
  exact h.2

theorem Instructions.wellFormed_account_lt
    (ix : Instructions) (accountLimit : Nat) (h : ix.wellFormed accountLimit = true) :
    ix.account.index < accountLimit := by
  simp [Instructions.wellFormed, Account.Handle.wellFormed] at h
  exact h.1.1

theorem Instructions.wellFormed_serialized_ge_two
    (ix : Instructions) (accountLimit : Nat) (h : ix.wellFormed accountLimit = true) :
    2 ≤ ix.serializedBytes := by
  simp [Instructions.wellFormed] at h
  exact h.1.2

theorem instructionsKey_def :
    instructionsKey =
      Pubkey.ofWords 7408838205410486022 13889942742359136821
        11922530290679293121 35966925531 := rfl

end ProofForge.Svm.Sdk.Sysvar
