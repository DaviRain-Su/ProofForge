import ProofForge
import ProofForge.Evm.Keccak
import ProofForge.Evm.IR
import ProofForge.Evm.Emit
import ProofForge.Evm.Golden
import ProofForge.Golden

open ProofForge.Evm

#guard ProofForge.Evm.Keccak.keccak256HexOfString "" ==
  "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

#guard ProofForge.Evm.Keccak.selectorU64 "increment" 1 == "dd9a82bc"

#guard ProofForge.Evm.Keccak.selectorU64 "get" 0 == "6d4ce63c"

#guard ProofForge.Evm.Keccak.keccak256HexOfString "Tipped(uint64)" ==
  "a20b303e80124ead462817f3d5ce5513d6d36a9ea8085f2cf523499b54a820c3"

#guard ProofForge.Evm.Keccak.keccak256HexOfString "Incremented(uint64)" !=
  ProofForge.Evm.Keccak.keccak256HexOfString "Tipped(uint64)"

#guard ProofForge.Evm.Keccak.selectorU64 "deposit" 1 == "13765838"

#guard ProofForge.Evm.Keccak.selectorU64 "decrement" 1 == "f2df7647"

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedCounter with
  | .error _ => false
  | .ok p =>
      p.name == "Counter" &&
        p.slots.size == 1 &&
        p.constructor.paramCount == 1 &&
        (p.entries.find? (·.ixName == "increment")).map (·.selector) == some "dd9a82bc" &&
        (p.entries.find? (·.ixName == "get")).map (·.selector) == some "6d4ce63c" &&
        (p.entries.find? (·.ixName == "get")).map (·.view) == some true

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedClock with
  | .error reason => reason.contains "svm leaf"
  | .ok _ => false

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedTransfer with
  | .error reason => reason.contains "svm leaf"
  | .ok _ => false

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedMaybe with
  | .error _ => false
  | .ok p =>
      p.slots.size == 2 &&
        IR.hasOptionLeaves p &&
        (p.slots[0]?.map (·.name) == some "slot_tag")

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedFlag with
  | .error _ => false
  | .ok p =>
      (p.slots[0]?.map (·.width) == some 1) &&
        (p.slots[1]?.map (·.width) == some 8)

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedPair with
  | .error _ => false
  | .ok p =>
      p.constructor.ixName == "initialize" &&
        (p.entries.find? (·.ixName == "initBoth")).isSome &&
        p.slots.size == 2

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedCounter with
  | .error _ => false
  | .ok p =>
      ProofForge.Evm.IR.digestHex p == ProofForge.Evm.IR.digestHex p &&
        ProofForge.Evm.IR.digestHex p !=
          ProofForge.Core.IR.digestHex ProofForge.Golden.extractedCounter

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedCounter,
        ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedPair with
  | .ok a, .ok b => ProofForge.Evm.IR.digestHex a != ProofForge.Evm.IR.digestHex b
  | _, _ => false

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedCounter with
  | .error _ => false
  | .ok p =>
      let q : ProofForge.Evm.IR.Program :=
        { p with entries := p.entries.map fun m =>
            if m.ixName == "get" then
              { m with ops := #[.returnU64 (.lit 0)] }
            else m }
      ProofForge.Evm.IR.digestHex p != ProofForge.Evm.IR.digestHex q

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedCounter with
  | .error _ => false
  | .ok p =>
      match ProofForge.Evm.Emit.emitYul p with
      | .error _ => false
      | .ok yul =>
          yul.contains "object \"Counter\"" &&
            yul.contains "case 0xdd9a82bc" &&
            yul.contains "case 0x6d4ce63c" &&
            yul.contains "case 0xf2df7647" &&
            yul.contains "sub(0xffffffffffffffff" &&
            yul.contains "sstore(0," &&
            yul.contains "revert(0, 0)" &&
            yul.contains s!"digest={ProofForge.Evm.IR.digestHex p}"

#guard
  let source : ProofForge.Core.IR.Program :=
    { ProofForge.Golden.extractedCounter with
      name := "ValueArith"
      methods := ProofForge.Golden.extractedCounter.methods.map fun m =>
        if m.ixName == "get" then
          { m with ops := #[.returnU64
              (.modU64 (.divU64 (.mulU64 (.lit 6) (.lit 7)) (.lit 3)) (.lit 5))] }
        else m }
  match ProofForge.Evm.IR.fromProgram source with
  | .error _ => false
  | .ok p =>
      match ProofForge.Evm.Emit.emitYul p with
      | .error _ => false
      | .ok yul =>
          yul.contains "if and(" && yul.contains " := mul(" &&
            yul.contains " := div(" && yul.contains " := mod(" &&
            yul.contains "if iszero("

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedCounter with
  | .error _ => false
  | .ok p =>
      let abi := ProofForge.Evm.Emit.emitAbi p
      abi.contains "\"type\":\"constructor\"" &&
        abi.contains "\"name\":\"increment\"" &&
        abi.contains "\"stateMutability\":\"view\""

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedPair with
  | .error _ => false
  | .ok p =>
      match ProofForge.Evm.Emit.emitYul p with
      | .error _ => false
      | .ok yul =>
          let both :=
            match yul.splitOn "case 0x8ced0f9f" with
            | _ :: rest :: _ => rest
            | _ => ""
          both.contains "sstore(0, arg0)" &&
            both.contains "sstore(1, arg1)" &&
            !both.contains "return(0, 32)\n        sstore(1"

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedFlag with
  | .error _ => false
  | .ok p =>
      match ProofForge.Evm.Emit.emitYul p with
      | .error _ => false
      | .ok yul =>
          yul.contains "and(sload(0), 0xff)" &&
            yul.contains "sstore(0, and(" &&
            yul.contains "sstore(1, ctor_arg0)"

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedMaybe with
  | .error _ => false
  | .ok p =>
      match ProofForge.Evm.Emit.emitYul p with
      | .error _ => false
      | .ok yul =>
          yul.contains "sstore(0, 1)" &&
            yul.contains "sstore(1, arg0)" &&
            yul.contains "sstore(0, 0)" &&
            yul.contains "sstore(1, 0)"
