import ProofForge.IR
import ProofForge.Sha256

namespace ProofForge.Idl

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
  u64LeBytes (Sha256.first8Le (IR.discPreimage ixName paramCount))

def layoutDiscBytes (p : IR.Program) : Array Nat :=
  u64BeBytes (Sha256.first8Be (IR.layoutPreimage p))

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
private def ixAccounts (p : IR.Program) (m : IR.Method) : String :=
  let n := Nat.max 1 (IR.cpiAccountCount p)
  let view := m.kind == .get
  let items :=
    (List.range n).map fun i =>
      let name := if i == 0 then "state" else s!"acc{i}"
      accJson name (!view && i == 0) (!view && i == 0)
  "[" ++ String.intercalate ", " items ++ "]"

private def instructionJson (p : IR.Program) (m : IR.Method) : String :=
  "    {\n" ++
    "      \"name\": \"" ++ escapeJson m.ixName ++ "\",\n" ++
    "      \"discriminator\": " ++ bytesJson (discBytes m.ixName m.paramCount) ++ ",\n" ++
    "      \"accounts\": " ++ ixAccounts p m ++ ",\n" ++
    "      \"args\": " ++ argsJson m.paramCount ++ "\n" ++
    "    }"

private def fieldJson (s : IR.Slot) : String :=
  "{\"name\":\"" ++ escapeJson s.name ++ "\",\"type\":\"" ++ idlTypeOfAbi s.abi ++ "\"}"

private def typesJson (p : IR.Program) : String :=
  let fields := String.intercalate ", " (p.slots.map fieldJson).toList
  "    {\n" ++
    "      \"name\": \"State\",\n" ++
    "      \"type\": {\n" ++
    "        \"kind\": \"struct\",\n" ++
    "        \"fields\": [" ++ fields ++ "]\n" ++
    "      }\n" ++
    "    }"

/-- Solana IDL spec 0.1.0。`address` 是 32 个 1，部署后替换。 -/
def emitIdl (p : IR.Program) : String :=
  let ixs := String.intercalate ",\n" (p.methods.map (instructionJson p)).toList
  "{\n" ++
    "  \"address\": \"11111111111111111111111111111111\",\n" ++
    "  \"metadata\": {\n" ++
    "    \"name\": \"" ++ escapeJson p.name ++ "\",\n" ++
    "    \"version\": \"0.0.1\",\n" ++
    "    \"spec\": \"0.1.0\",\n" ++
    "    \"description\": \"Created with ProofForge\"\n" ++
    "  },\n" ++
    "  \"instructions\": [\n" ++ ixs ++ "\n" ++
    "  ],\n" ++
    "  \"accounts\": [\n" ++
    "    {\n" ++
    "      \"name\": \"State\",\n" ++
    "      \"discriminator\": " ++ bytesJson (layoutDiscBytes p) ++ "\n" ++
    "    }\n" ++
    "  ],\n" ++
    "  \"types\": [\n" ++ typesJson p ++ "\n" ++
    "  ]\n" ++
    "}\n"

end ProofForge.Idl
