import ProofForge.Crypto.Sha256
import ProofForge.Svm.ABI
import ProofForge.Svm.IR

namespace ProofForge.Svm.Idl

open ProofForge.Crypto

/-- Anchor / Solana IDL spec `0.1.0`。地址占位，部署后再填。 -/

private def escapeJson (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\""

private def u64LeBytes (n : UInt64) : Array Nat :=
  (List.range 8).toArray.map fun i =>
    ((n >>> UInt64.ofNat (8 * i)) &&& 255).toNat

private def u64BeBytes (n : UInt64) : Array Nat :=
  (List.range 8).toArray.map fun i =>
    ((n >>> UInt64.ofNat (8 * (7 - i))) &&& 255).toNat

private def bytesJson (bs : Array Nat) : String :=
  "[" ++ String.intercalate ", " (bs.map toString).toList ++ "]"

def discBytes (ixName : String) (paramCount : Nat) : Array Nat :=
  u64LeBytes (Sha256.first8Le (ABI.discPreimage ixName paramCount))

private def sourceSlots (p : IR.Program) : Array Core.IR.Slot :=
  p.slots.map fun slot =>
    { name := slot.name, width := slot.width, abi := slot.abi }

def layoutDiscBytesOf (slots : Array Core.IR.Slot) : Array Nat :=
  u64BeBytes (Sha256.first8Be (ABI.layoutPreimageOf slots))

def layoutDiscBytesProgram (p : IR.Program) : Array Nat :=
  layoutDiscBytesOf (sourceSlots p)

/-- Compatibility wrapper for callers that still own the old extraction IR. -/
def layoutDiscBytes (p : Extract.Legacy.Program) : Array Nat :=
  u64BeBytes (Sha256.first8Be (ABI.layoutPreimage p))

private def idlTypeOfAbi (abi : String) : String :=
  if abi.startsWith "u8" then "u8"
  else if abi.startsWith "u16" then "u16"
  else if abi.startsWith "u32" then "u32"
  else "u64"

private def argJson (i : Nat) : String :=
  "{\"name\":\"arg" ++ toString i ++ "\",\"type\":\"u64\"}"

private def argsJson (paramCount : Nat) : String :=
  "[" ++ String.intercalate ", " ((List.range paramCount).map argJson) ++ "]"

private def accJson (name : String) (writable signer : Bool) : String :=
  let w := if writable then ",\"writable\":true" else ""
  let s := if signer then ",\"signer\":true" else ""
  "{\"name\":\"" ++ escapeJson name ++ "\"" ++ w ++ s ++ "}"

/-- 外层账户：acc0 是 state。CPI 程序再列 acc1…。旗是保守默认，不是每条 recipe 的 metas。 -/
private def ixAccounts (accountCount : Nat) (kind : Core.IR.MethodKind) : String :=
  let n := Nat.max 1 accountCount
  let view := kind == .get
  let items :=
    (List.range n).map fun i =>
      let name := if i == 0 then "state" else s!"acc{i}"
      accJson name (!view && i == 0) (!view && i == 0)
  "[" ++ String.intercalate ", " items ++ "]"

private def instructionJson (accountCount : Nat) (kind : Core.IR.MethodKind)
    (ixName : String) (paramCount : Nat) : String :=
  "    {\n" ++
    "      \"name\": \"" ++ escapeJson ixName ++ "\",\n" ++
    "      \"discriminator\": " ++ bytesJson (discBytes ixName paramCount) ++ ",\n" ++
    "      \"accounts\": " ++ ixAccounts accountCount kind ++ ",\n" ++
    "      \"args\": " ++ argsJson paramCount ++ "\n" ++
    "    }"

private def fieldJson (name abi : String) : String :=
  "{\"name\":\"" ++ escapeJson name ++ "\",\"type\":\"" ++ idlTypeOfAbi abi ++ "\"}"

private def typesJson (fields : String) : String :=
  "    {\n" ++
    "      \"name\": \"State\",\n" ++
    "      \"type\": {\n" ++
    "        \"kind\": \"struct\",\n" ++
    "        \"fields\": [" ++ fields ++ "]\n" ++
    "      }\n" ++
    "    }"

private def render (name instructions fields : String) (layoutDisc : Array Nat) : String :=
  "{\n" ++
    "  \"address\": \"11111111111111111111111111111111\",\n" ++
    "  \"metadata\": {\n" ++
    "    \"name\": \"" ++ escapeJson name ++ "\",\n" ++
    "    \"version\": \"0.0.1\",\n" ++
    "    \"spec\": \"0.1.0\",\n" ++
    "    \"description\": \"Created with ProofForge\"\n" ++
    "  },\n" ++
    "  \"instructions\": [\n" ++ instructions ++ "\n" ++
    "  ],\n" ++
    "  \"accounts\": [\n" ++
    "    {\n" ++
    "      \"name\": \"State\",\n" ++
    "      \"discriminator\": " ++ bytesJson layoutDisc ++ "\n" ++
    "    }\n" ++
    "  ],\n" ++
    "  \"types\": [\n" ++ typesJson fields ++ "\n" ++
    "  ]\n" ++
    "}\n"

/-- Solana IDL spec 0.1.0 from the target-owned SVM program. -/
def emitProgramIdl (p : IR.Program) : String :=
  let accountCount := IR.cpiAccountCount p
  let instructions := String.intercalate ",\n" <| p.methods.toList.map fun method =>
    instructionJson accountCount method.kind method.ixName method.paramCount
  let fields := String.intercalate ", " <| p.slots.toList.map fun slot =>
    fieldJson slot.name slot.abi
  render p.name instructions fields (layoutDiscBytesProgram p)

/-- Compatibility entry point for the old extraction IR. -/
def emitIdl (p : Extract.Legacy.Program) : String :=
  let accountCount := ABI.cpiAccountCount p
  let instructions := String.intercalate ",\n" <| p.methods.toList.map fun method =>
    instructionJson accountCount method.kind method.ixName method.paramCount
  let fields := String.intercalate ", " <| p.slots.toList.map fun slot =>
    fieldJson slot.name slot.abi
  render p.name instructions fields (layoutDiscBytes p)

end ProofForge.Svm.Idl
