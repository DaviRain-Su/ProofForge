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

/-- External accounts written directly or through CPI by one instruction. Direct account-data
effects use physical indexes; CPI metas are relative to the region after state. -/
private partial def writtenAccounts (ops : Array IR.Op) : Array Nat :=
  ops.foldl (init := #[]) fun accounts op =>
    let here :=
      match op with
      | .invoke _ metas _ _ _ =>
          metas.filterMap fun entry => if entry.writable then some (entry.acc + 1) else none
      | .accDataWordSetAt acc .. | .accDataRbTreeKey4Insert acc ..
      | .accDataRbTreeKey4Remove acc .. | .accDataRbTreeOrderInsert acc ..
      | .accDataRbTreeOrderRemove acc .. => #[acc]
      | _ => #[]
    let nested :=
      match op with
      | .ite _ _ _ thn els => writtenAccounts thn ++ writtenAccounts els
      | .forBody _ body => writtenAccounts body
      | _ => #[]
    accounts ++ here ++ nested

/-- 外层账户：acc0 是 state。额外 writable flag 来自该 instruction 的实际 effect。 -/
private def ixAccounts (accountCount : Nat) (kind : Core.IR.MethodKind)
    (written : Array Nat) : String :=
  let n := Nat.max 1 accountCount
  let view := kind == .get
  let items :=
    (List.range n).map fun i =>
      let name := if i == 0 then "state" else s!"acc{i}"
      accJson name ((!view && i == 0) || written.any (· == i)) (!view && i == 0)
  "[" ++ String.intercalate ", " items ++ "]"

private def instructionJson (accountCount : Nat) (kind : Core.IR.MethodKind)
    (written : Array Nat) (ixName : String) (paramCount : Nat) : String :=
  "    {\n" ++
    "      \"name\": \"" ++ escapeJson ixName ++ "\",\n" ++
    "      \"discriminator\": " ++ bytesJson (discBytes ixName paramCount) ++ ",\n" ++
    "      \"accounts\": " ++ ixAccounts accountCount kind written ++ ",\n" ++
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

/-- Render target-owned SVM instruction and slot metadata as a Solana IDL. -/
private def emitIdlOfWrites (name : String) (accountCount : Nat)
    (methods : Array (Core.IR.MethodKind × String × Nat))
    (writes : Array (Array Nat))
    (slots : Array Core.IR.Slot) (layoutDisc : Array Nat) : String :=
  let instructions := String.intercalate ",\n" <| (methods.zip writes).toList.map fun entry =>
    let method := entry.1
    instructionJson accountCount method.1 entry.2 method.2.1 method.2.2
  let fields := String.intercalate ", " <| slots.toList.map fun slot =>
    fieldJson slot.name slot.abi
  render name instructions fields layoutDisc

/-- Render target-owned SVM instruction and slot metadata as a Solana IDL. -/
def emitIdlOf (name : String) (accountCount : Nat)
    (methods : Array (Core.IR.MethodKind × String × Nat))
    (slots : Array Core.IR.Slot) (layoutDisc : Array Nat) : String :=
  emitIdlOfWrites name accountCount methods (Array.replicate methods.size #[]) slots layoutDisc

/-- Solana IDL spec 0.1.0 from the target-owned SVM program. -/
def emitProgramIdl (p : IR.Program) : String :=
  let methods := p.methods.map fun method =>
    (method.kind, method.ixName, method.paramCount)
  let writes := p.methods.map fun method => writtenAccounts method.ops
  emitIdlOfWrites p.name (IR.cpiAccountCount p) methods writes
    (sourceSlots p) (layoutDiscBytesProgram p)

end ProofForge.Svm.Idl
