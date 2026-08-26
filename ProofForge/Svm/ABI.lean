import ProofForge.Core.IR
import ProofForge.Crypto.Sha256
import ProofForge.Svm.Ops

namespace ProofForge.Svm.ABI

open ProofForge.Crypto

/-- Agave's currently enforced transaction account-lock limit. -/
def maxTxAccountLocks : Nat := ProofForge.Svm.Ops.maxTxAccountLocks

/-- One slot is reserved from the 256 transaction-account entries for `NON_DUP_MARKER`. -/
def maxAccountsPerInstruction : Nat := 255

def accInRange (acc : Nat) : Bool :=
  ProofForge.Svm.Ops.accInRange acc

def ixParamSig (paramCount : Nat) : String :=
  String.intercalate "," (List.replicate paramCount "u64")

/-- `sha256("proof-forge-solana-v1:" ++ name ++ "(" ++ sig ++ ")")` input. -/
def discPreimage (ixName : String) (paramCount : Nat) : String :=
  s!"proof-forge-solana-v1:{ixName}({ixParamSig paramCount})"

def discHexOf (ixName : String) (paramCount : Nat) : Except String String :=
  .ok s!"0x{Core.IR.u64Hex (Sha256.first8Le (discPreimage ixName paramCount))}"

def discFirstByte (ixName : String) (paramCount : Nat) : Nat :=
  (Sha256.first8Le (discPreimage ixName paramCount) &&& 255).toNat

/-- Physical SVM field offset for target-neutral source slots. -/
def fieldOffsetOf (slots : Array Core.IR.Slot) (name : String) : Option Nat :=
  Id.run do
    let mut offset : Nat := 8
    for slot in slots do
      if slot.name == name then return some offset
      offset := offset + slot.width
    return none

def dataLenOf (slots : Array Core.IR.Slot) : Nat :=
  let raw := 8 + slots.foldl (init := 0) fun acc slot => acc + slot.width
  raw + (8 - raw % 8) % 8

/-- Loader V3 single-account data begins at `0x60`. -/
def acc0Data : Nat := 0x60
def maxPermittedDataIncrease : Nat := 10240

structure InputLayout where
  rentEpoch : Nat
  instructionDataLen : Nat
  instructionData : Nat
  deriving BEq, Repr, Inhabited

def accountPrefix : Nat := 0x58

def accountSpan (accountDataLen : Nat) : Nat :=
  let dataEnd := accountPrefix + accountDataLen + maxPermittedDataIncrease
  dataEnd + (8 - dataEnd % 8) % 8 + 8

def inputLayoutOf (accountDataLen : Nat) (walk : Bool) (accountCount : Nat) : InputLayout :=
  if walk then
    let rec lastRent (remaining : Nat) (offset : Nat) : Nat :=
      match remaining with
      | 0 => offset - 8
      | remaining' + 1 => lastRent remaining' (offset + accountSpan 0)
    let rent := lastRent accountCount 8
    { rentEpoch := rent, instructionDataLen := rent + 8, instructionData := rent + 16 }
  else
    let dataEnd := acc0Data + accountDataLen + maxPermittedDataIncrease
    let rent := dataEnd + (8 - dataEnd % 8) % 8
    { rentEpoch := rent, instructionDataLen := rent + 8, instructionData := rent + 16 }

def layoutSlotName (name : String) : String :=
  if name == "value" then "count" else name

def layoutSigOf (slots : Array Core.IR.Slot) : String :=
  let parts := Id.run do
    let mut result : Array String := #[]
    let mut index : Nat := 0
    let mut offset : Nat := 8
    for slot in slots do
      result := result.push
        s!"{index}:{layoutSlotName slot.name}:0:{offset}:{slot.width}:{slot.abi}"
      offset := offset + slot.width
      index := index + 1
    return result
  s!"{slots.size}|{String.intercalate "|" parts.toList}"

def layoutPreimageOf (slots : Array Core.IR.Slot) : String :=
  s!"proof-forge-solana-layout-v1:{layoutSigOf slots}"

def layoutMarkerHexOf (slots : Array Core.IR.Slot) : Except String String :=
  .ok s!"0x{Core.IR.u64Hex (Sha256.first8Be (layoutPreimageOf slots))}"

end ProofForge.Svm.ABI
