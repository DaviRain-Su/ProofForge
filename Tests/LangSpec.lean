import Examples.Lang

namespace Tests.LangSpec

open Examples.Lang

#guard (init 7).cells[0]! == 7
#guard get (init 7) == 7
#guard band (init 0) 0xf0 0x0f == 0
#guard bor (init 0) 0xf0 0x0f == 0xff
#guard bxor (init 0) 0xff 0x0f == 0xf0
#guard bnot (init 0) 0 == u64Max
#guard shl (init 0) 1 3 == 8
#guard shr (init 0) 8 3 == 1
#guard mask8 (init 0) 7 == 7
#guard
  match both (init 9) with
  | (a, b) => a == 9 && b == 0

#guard
  match SolanaLean.Evm.IR.fromProgram SolanaLean.Golden.extractedLang with
  | .error _ => false
  | .ok p =>
      match SolanaLean.Evm.Emit.emitYul p with
      | .error _ => false
      | .ok yul =>
          yul.contains "and(" &&
            yul.contains "shl(" &&
            yul.contains "if gt(" &&
            yul.contains "for { let " &&
            yul.contains "sload(add(" &&
            yul.contains "sstore(add(" &&
            yul.contains "revert(0, 4)" &&
            yul.contains "return(0, 64)" &&
            yul.contains "if gt(arg0, 0xff)"

#guard
  match SolanaLean.Evm.IR.fromProgram SolanaLean.Golden.extractedLang with
  | .error _ => false
  | .ok p =>
      (p.entries.find? (·.ixName == "mask8")).map (·.paramWidths) == some #[1] &&
        (p.entries.find? (·.ixName == "both")).map (·.retCount) == some 2

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedLang with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

#guard SolanaLean.Evm.Keccak.selector "mask8" #["uint8"] ==
  SolanaLean.Evm.Keccak.selectorOfWidths "mask8" #[1]

end Tests.LangSpec
