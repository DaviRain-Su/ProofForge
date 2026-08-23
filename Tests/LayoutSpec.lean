import ProofForge
import Examples.Flag
import Examples.Maybe

#pf_build Examples.Flag

#pf_build Examples.Maybe

#guard
  match ProofForge.Svm.ABI.fieldOffset
      { name := "Flag"
        slots := #[{ name := "flag", width := 1, abi := "u8-le" }, { name := "count" }]
        methods := #[] } "count" with
  | some 9 => true
  | _ => false

#guard
  let p : ProofForge.Core.IR.Program :=
    { name := "Maybe"
      slots := #[{ name := "slot_tag" }, { name := "slot_p0" }]
      methods := #[] }
  ProofForge.Svm.ABI.fieldOffset p "slot_p0" == some 16 &&
    ProofForge.Svm.ABI.dataLen p == 24

#guard
  match ProofForge.Svm.ABI.layoutMarkerHex
      { name := "Flag"
        slots := #[{ name := "flag", width := 1, abi := "u8-le" }, { name := "count" }]
        methods := #[] } with
  | .ok "0x2ac58f7fa0191d14" => true
  | _ => false

#guard
  match ProofForge.Svm.ABI.layoutMarkerHex
      { name := "Maybe"
        slots := #[{ name := "slot_tag" }, { name := "slot_p0" }]
        methods := #[] } with
  | .ok "0xf53e0f4e232b2e90" => true
  | _ => false

#guard
  match ProofForge.Svm.ABI.discHexOf "setFlag" 1 with
  | .ok "0xabc0ed57af4c46fe" => true
  | _ => false

#guard
  match ProofForge.Svm.ABI.discHexOf "isSome" 0 with
  | .ok "0xae9916c18320fcc3" => true
  | _ => false

#guard
  match ProofForge.Svm.ABI.discHexOf "neverSeen" 2 with
  | .ok "0xf53bae450cc55143" => true
  | _ => false

#guard
  ProofForge.Core.IR.digestHex ProofForge.Golden.extractedFlag ==
    ProofForge.Core.IR.digestHex ProofForge.Golden.extractedFlag

#guard
  ProofForge.Core.IR.digestHex ProofForge.Golden.extractedFlag !=
    ProofForge.Core.IR.digestHex ProofForge.Golden.extractedMaybe

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedFlag with
  | .error _ => false
  | .ok asm =>
      asm.contains "stxb" &&
        asm.contains "ldxb" &&
        asm.contains "0x2ac58f7fa0191d14" &&
        asm.contains "digest=" &&
        asm.contains "call setFlag"

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedMaybe with
  | .error _ => false
  | .ok asm =>
      asm.contains "0xf53e0f4e232b2e90" &&
        asm.contains "call setNone" &&
        asm.contains "call setSome" &&
        asm.contains "call isSome"
