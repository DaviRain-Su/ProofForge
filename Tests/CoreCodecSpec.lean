import ProofForge.Core.Codec
import ProofForge.Core.Value
import ProofForge.Evm.Codec
import ProofForge.Evm.IR
import ProofForge.Extract

namespace Tests.CoreCodecSpec

open ProofForge
open ProofForge.Core.Codec
open Lean Elab Command

namespace BoundaryValues

open ProofForge.Core.Value

def echo128 (_state : UInt64) (value : UInt128) : UInt128 := value

def echo256 (_state : UInt64) (value : ProofForge.Core.Value.UInt256) :
    ProofForge.Core.Value.UInt256 := value

def echo12 (_state : UInt64) (value : FixedBytes 12) : FixedBytes 12 := value

def echoEvm256 (_state : UInt64) (value : ProofForge.Evm.Runtime.UInt256) :
    ProofForge.Evm.Runtime.UInt256 := value

def echoEvmBytes32 (_state : UInt64) (value : ProofForge.Evm.Runtime.Bytes32) :
    ProofForge.Evm.Runtime.Bytes32 := value

def invalidBytes0 (_state : UInt64) (value : FixedBytes 0) : FixedBytes 0 := value

def invalidBytes33 (_state : UInt64) (value : FixedBytes 33) : FixedBytes 33 := value

def dynamicBytes (n : Nat) (_state : UInt64) (value : FixedBytes n) : FixedBytes n := value

elab "#pf_guard_shared_boundary_values" : command => do
  let env ← getEnv
  let check (name : Name) (type : Core.Codec.Scalar) (limbs : Array String) := do
    let method ←
      match Extract.extractMethod env .get name with
      | .ok method => pure method
      | .error reason => throwError reason
    let mut opsMatch := method.ops.size == limbs.size
    for i in [:limbs.size] do
      match method.ops[i]! with
      | .returnU64 (.field (.arg 0) limb) =>
          unless limb == limbs[i]! do opsMatch := false
      | _ => opsMatch := false
    unless method.paramTypes == #[type] && method.retTypes == #[type] &&
        method.retCount == limbs.size && opsMatch do
      throwError s!"wrong shared boundary metadata for {name}"
  check ``echo128 .uint128 #["w0", "w1"]
  check ``echo256 .uint256 #["w0", "w1", "w2", "w3"]
  check ``echo12 (.fixedBytes 12) #["w0", "w1"]
  check ``echoEvm256 .uint256 #["w0", "w1", "w2", "w3"]
  check ``echoEvmBytes32 .bytes32 #["w0", "w1", "w2", "w3"]
  for name in [``invalidBytes0, ``invalidBytes33, ``dynamicBytes] do
    match Extract.inferKind env name with
    | .error reason =>
        unless reason.contains "cannot classify" do
          throwError s!"wrong invalid FixedBytes rejection for {name}: {reason}"
    | .ok _ => throwError s!"invalid FixedBytes shape was accepted for {name}"

#pf_guard_shared_boundary_values

#guard FixedBytes.validSize 1
#guard FixedBytes.validSize 32
#guard !FixedBytes.validSize 0
#guard !FixedBytes.validSize 33
#guard FixedBytes.limbCount 12 == 2
#guard FixedBytes.limbCount 32 == 4
#guard ProofForge.Evm.Runtime.UInt256.mk 1 2 3 4 == ⟨1, 2, 3, 4⟩
#guard ProofForge.Evm.Runtime.Bytes32.mk 1 2 3 4 == ⟨1, 2, 3, 4⟩

end BoundaryValues

private def orderBatch : Schema :=
  .record "OrderBatch" #[
    ("market", .scalar .address32),
    ("orders", .boundedArray 4 (.scalar .uint64))
  ]

#guard Scalar.isWellFormed .uint256
#guard Scalar.isWellFormed .boolean
#guard Scalar.isWellFormed (.fixedBytes 32)
#guard !Scalar.isWellFormed (.uint 7)
#guard !Scalar.isWellFormed (.fixedBytes 0)

#guard
  match analyze orderBatch with
  | .ok usage =>
      usage.descriptorNodes == 4 && usage.logicalLeaves == 6 && usage.depth == 3
  | .error _ => false

#guard
  match validate (.record "Bad" #[
      ("same", .scalar .uint64),
      ("same", .scalar .uint64)
    ]) with
  | .error reason => reason.contains "unique"
  | .ok _ => false

#guard
  match validate (.boundedArray 4097 (.scalar .uint64)) with
  | .error reason => reason.contains "capacity"
  | .ok _ => false

#guard
  match analyze (.enumeration "Side" 8 #[
      ("Bid", .unit),
      ("Ask", .unit)
    ]) with
  | .ok usage => usage.logicalLeaves == 1
  | .error _ => false

#guard match ProofForge.Evm.Codec.abiType .address20 with
  | .ok name => name == "address"
  | .error _ => false
#guard match ProofForge.Evm.Codec.abiType .bytes32 with
  | .ok name => name == "bytes32"
  | .error _ => false
#guard match ProofForge.Evm.Codec.scalarOfLegacyWidth 33 with
  | .ok type => type == .bytes32
  | .error _ => false
#guard match ProofForge.Evm.Codec.wordGuard (.fixedBytes 12) with
  | .ok guard => guard == .fixedBytesLeftPadded 12
  | .error _ => false

private def typedMethod : ProofForge.Evm.IR.Method := {
  kind := .get
  name := "typed"
  ixName := "typed"
  paramCount := 1
  paramWidths := #[8]
  paramTypes := #[.address20]
}

#guard match typedMethod.resolvedParamTypes with
  | .ok types => types == #[.address20]
  | .error _ => false

private def incompleteMethod : ProofForge.Evm.IR.Method := {
  kind := .get
  name := "incomplete"
  ixName := "incomplete"
  paramCount := 2
  paramWidths := #[8]
}

#guard
  match incompleteMethod.resolvedParamTypes with
  | .error reason => reason.contains "incomplete"
  | .ok _ => false

end Tests.CoreCodecSpec
