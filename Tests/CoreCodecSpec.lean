import ProofForge.Core.Codec
import ProofForge.Core.Value
import ProofForge.Evm.Codec
import ProofForge.Evm.Emit
import ProofForge.Evm.IR
import ProofForge.Extract
import ProofForge.Svm.IR

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
        method.paramSchemas == #[.scalar type] && method.retSchema == .scalar type &&
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

namespace AggregateBoundary

open ProofForge.Core.Value

structure Request where
  amount : UInt64
  enabled : Bool

inductive Action where
  | cancel
  | place (lots : UInt64) (clientId : FixedBytes 12)

def inspect (_state : UInt64) (_request : Request) (_pair : UInt32 × Bool)
    (_maybe : Option (UInt64 × Bool)) (_items : Vector UInt16 3) (_action : Action)
    (_unit : Unit) : UInt64 := 0

def pairResult (_state : UInt64) : UInt64 × Bool := (7, true)

inductive Recursive where
  | next (tail : Recursive)

structure Parent where
  parent : UInt64

structure Inherited extends Parent where
  child : UInt64

structure Box (α : Type) where
  value : α

def dynamicArray (_state : UInt64) (_items : Array UInt64) : UInt64 := 0
def recursive (_state : UInt64) (_value : Recursive) : UInt64 := 0
def inherited (_state : UInt64) (_value : Inherited) : UInt64 := 0
def polymorphic (_state : UInt64) (_value : Box UInt64) : UInt64 := 0
def overBudget (_state : UInt64) (_value : Vector UInt64 4097) : UInt64 := 0

elab "#pf_guard_aggregate_boundary_schemas" : command => do
  let env ← getEnv
  let method ←
    match Extract.extractMethod env .get ``inspect with
    | .ok method => pure method
    | .error reason => throwError reason
  let expected : Array Schema := #[
    .record (``Request).toString #[
      ("amount", .scalar .uint64),
      ("enabled", .scalar .boolean)
    ],
    .tuple #[.scalar .uint32, .scalar .boolean],
    .option (.tuple #[.scalar .uint64, .scalar .boolean]),
    .fixedArray 3 (.scalar .uint16),
    .enumeration (``Action).toString 8 #[
      ("cancel", .unit),
      ("place", .tuple #[.scalar .uint64, .scalar (.fixedBytes 12)])
    ],
    .unit
  ]
  unless method.paramSchemas == expected && method.paramTypes.isEmpty &&
      method.paramWidths.isEmpty do
    throwError s!"wrong aggregate parameter schemas: {repr method.paramSchemas}"
  let result ←
    match Extract.extractMethod env .get ``pairResult with
    | .ok result => pure result
    | .error reason => throwError reason
  unless result.retSchema == .tuple #[.scalar .uint64, .scalar .boolean] &&
      result.retTypes.isEmpty && result.retCount == 2 do
    throwError s!"wrong aggregate result schema: {repr result.retSchema}"
  let reject (name : Name) (fragment : String) :=
    match Extract.extractMethod env .get name with
    | .error reason =>
        unless reason.contains fragment do
          throwError s!"wrong boundary rejection for {name}: {reason}"
    | .ok _ => throwError s!"unsupported boundary shape was accepted for {name}"
  reject ``dynamicArray "dynamic"
  reject ``recursive "recursive"
  reject ``inherited "inheritance"
  reject ``polymorphic "polymorphic"
  reject ``overBudget "array length"
  let init : Extract.IR.Method := {
    kind := .init
    name := "AggregateGate.init"
    ixName := "initialize"
    retSchema := .unit
    ops := #[.returnState (.lit 0)]
  }
  let aggregate : Extract.IR.Method := {
    kind := .get
    name := "AggregateGate.read"
    ixName := "read"
    paramCount := 1
    paramSchemas := #[.tuple #[.scalar .uint64, .scalar .boolean]]
    retTypes := #[.uint64]
    retSchema := .scalar .uint64
    ops := #[.returnU64 (.lit 0)]
  }
  let program : Extract.IR.Program := {
    name := "AggregateGate"
    slots := #[{ name := "value" }]
    methods := #[init, aggregate]
  }
  match ProofForge.Svm.IR.fromExtracted program with
  | .error reason =>
      unless reason.contains "aggregate parameter binding" do
        throwError s!"wrong SVM aggregate gate: {reason}"
  | .ok _ => throwError "SVM accepted an unbound aggregate parameter"
  match ProofForge.Evm.IR.fromExtracted program with
  | .error reason => throwError s!"EVM rejected a static aggregate parameter: {reason}"
  | .ok lowered =>
      let some read := lowered.entries.find? (·.ixName == "read")
        | throwError "EVM static aggregate entry is missing"
      unless read.logicalParamCount == 1 && read.paramCount == 2 &&
          read.paramTypes == #[.uint64, .boolean] &&
          read.selector == ProofForge.Crypto.Keccak.selector "read" #["(uint64,bool)"] do
        throwError s!"wrong EVM static aggregate binding: {repr read}"
  let tagged := { aggregate with
    paramSchemas := #[.option (.scalar .uint64)]
    ops := #[.returnU64 (.lit 0)]
  }
  match ProofForge.Evm.IR.fromExtracted { program with methods := #[init, tagged] } with
  | .error reason =>
      unless reason.contains "option ABI tags" do
        throwError s!"wrong EVM tagged aggregate rejection: {reason}"
  | .ok _ => throwError "EVM accepted an Option without an ABI tag policy"
  let wideResult : Extract.IR.Method := {
    kind := .get
    name := "AggregateGate.wideResult"
    ixName := "wideResult"
    retSchema := .tuple #[
      .scalar .uint128,
      .scalar (.fixedBytes 12),
      .scalar .address20
    ]
    retCount := 7
    ops := #[
      .returnU64 (.lit 1), .returnU64 (.lit 2),
      .returnU64 (.lit 3), .returnU64 (.lit 4),
      .returnU64 (.lit 5), .returnU64 (.lit 6), .returnU64 (.lit 7)
    ]
  }
  let wideProgram ←
    match ProofForge.Evm.IR.fromExtracted { program with methods := #[init, wideResult] } with
    | .ok lowered => pure lowered
    | .error reason => throwError s!"EVM rejected a wide aggregate result: {reason}"
  let wideYul ←
    match ProofForge.Evm.Emit.emitYul wideProgram with
    | .ok yul => pure yul
    | .error reason => throwError s!"EVM failed to emit a wide aggregate result: {reason}"
  unless wideYul.contains "pf_store_fixed_bytes(32," &&
      wideYul.contains "pf_store_addr20(64," && wideYul.contains "return(0, 96)" do
    throwError "EVM wide aggregate result packing is incomplete"

#pf_guard_aggregate_boundary_schemas

end AggregateBoundary

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

private def staticRequest : Schema :=
  .record "Request" #[
    ("amount", .scalar .uint64),
    ("pair", .tuple #[.scalar .uint32, .scalar .boolean]),
    ("levels", .fixedArray 2 (.scalar .uint16))
  ]

#guard
  match staticLeaves staticRequest with
  | .ok leaves =>
      leaves.map StaticLeaf.sourceName ==
        #["amount", "pair_fst", "pair_snd", "levels_0", "levels_1"] &&
      leaves.map (·.type) == #[.uint64, .uint32, .boolean, .uint16, .uint16] &&
      leaves[3]!.path == #[.field "levels", .index 0]
  | .error _ => false

#guard match staticLeaves .unit with
  | .ok leaves => leaves.isEmpty
  | .error _ => false

#guard
  match staticLeaves (.record "Ambiguous" #[
      ("pair_fst", .scalar .uint64),
      ("pair", .tuple #[.scalar .uint64, .scalar .uint64])
    ]) with
  | .ok leaves =>
      leaves.map StaticLeaf.sourceName == #["pair_fst", "pair_fst", "pair_snd"] &&
      leaves[0]!.path != leaves[1]!.path
  | .error _ => false

#guard
  match staticLeaves (.record "Ambiguous" #[
      ("pair_fst", .scalar .uint64),
      ("pair", .tuple #[.scalar .uint64, .scalar .uint64])
    ]) with
  | .error _ => false
  | .ok leaves =>
      match resolveSourceProjection leaves #[1, 1, 1]
          (fun | "w0" => some 0 | _ => none) "pair_fst" with
      | .error reason => reason.contains "missing or ambiguous"
      | .ok _ => false

#guard
  match staticLeaves (.option (.scalar .uint64)) with
  | .error reason => reason.contains "target-owned option tag policy"
  | .ok _ => false

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
#guard match ProofForge.Evm.Codec.abiTypeOfSchema staticRequest with
  | .ok type => type == "(uint64,(uint32,bool),uint16[2])"
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
