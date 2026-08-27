import ProofForge.Core.Codec
import ProofForge.Evm.Codec
import ProofForge.Evm.IR

namespace Tests.CoreCodecSpec

open ProofForge
open ProofForge.Core.Codec

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
