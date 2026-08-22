import SolanaLean
import Examples.Flag
import Examples.Maybe

#solana_build Examples.Flag

#solana_build Examples.Maybe

#guard
  match SolanaLean.IR.fieldOffset
      { name := "Flag"
        slots := #[{ name := "flag", width := 1, abi := "u8-le" }, { name := "count" }]
        methods := #[] } "count" with
  | some 9 => true
  | _ => false

#guard
  let p : SolanaLean.IR.Program :=
    { name := "Maybe"
      slots := #[{ name := "slot_tag" }, { name := "slot_p0" }]
      methods := #[] }
  SolanaLean.IR.fieldOffset p "slot_p0" == some 16 &&
    SolanaLean.IR.dataLen p == 24

#guard
  match SolanaLean.IR.layoutMarkerHex
      { name := "Flag"
        slots := #[{ name := "flag", width := 1, abi := "u8-le" }, { name := "count" }]
        methods := #[] } with
  | .ok "0x2ac58f7fa0191d14" => true
  | _ => false

#guard
  match SolanaLean.IR.layoutMarkerHex
      { name := "Maybe"
        slots := #[{ name := "slot_tag" }, { name := "slot_p0" }]
        methods := #[] } with
  | .ok "0xf53e0f4e232b2e90" => true
  | _ => false

#guard
  match SolanaLean.IR.discHexOf "setFlag" 1 with
  | .ok "0xabc0ed57af4c46fe" => true
  | _ => false

#guard
  match SolanaLean.IR.discHexOf "isSome" 0 with
  | .ok "0xae9916c18320fcc3" => true
  | _ => false

#guard
  SolanaLean.IR.digestHex SolanaLean.IR.extractedFlag ==
    SolanaLean.IR.digestHex SolanaLean.IR.extractedFlag

#guard
  SolanaLean.IR.digestHex SolanaLean.IR.extractedFlag !=
    SolanaLean.IR.digestHex SolanaLean.IR.extractedMaybe

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.IR.extractedFlag with
  | .error _ => false
  | .ok asm =>
      asm.contains "stxb" &&
        asm.contains "ldxb" &&
        asm.contains "0x2ac58f7fa0191d14" &&
        asm.contains "digest=" &&
        asm.contains "call setFlag"

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.IR.extractedMaybe with
  | .error _ => false
  | .ok asm =>
      asm.contains "0xf53e0f4e232b2e90" &&
        asm.contains "call setNone" &&
        asm.contains "call setSome" &&
        asm.contains "call isSome"
