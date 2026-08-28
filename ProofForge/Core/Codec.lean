namespace ProofForge.Core.Codec

/-- Target-neutral scalar values at a contract boundary.  This is logical
metadata: targets still own their physical ABI/Borsh encoding. -/
inductive Scalar where
  | boolean
  | uint (bits : Nat)
  | address (bytes : Nat)
  | fixedBytes (bytes : Nat)
  deriving Repr, BEq, Inhabited

namespace Scalar

def isWellFormed : Scalar → Bool
  | .boolean => true
  | .uint bits => 8 ≤ bits && bits ≤ 256 && bits % 8 == 0
  | .address bytes | .fixedBytes bytes => 1 ≤ bytes && bytes ≤ 32

def byteWidth : Scalar → Nat
  | .boolean => 1
  | .uint bits => bits / 8
  | .address bytes | .fixedBytes bytes => bytes

def uint8 : Scalar := .uint 8
def uint16 : Scalar := .uint 16
def uint32 : Scalar := .uint 32
def uint64 : Scalar := .uint 64
def uint128 : Scalar := .uint 128
def uint256 : Scalar := .uint 256
def address20 : Scalar := .address 20
def address32 : Scalar := .address 32
def bytes32 : Scalar := .fixedBytes 32

end Scalar

/-- Logical codec shape shared by extractors and target adapters.  It does not
describe SVM account offsets or EVM storage slots. -/
inductive Schema where
  | unit
  | scalar (type : Scalar)
  | tuple (items : Array Schema)
  | record (name : String) (fields : Array (String × Schema))
  | enumeration (name : String) (tagBits : Nat) (variants : Array (String × Schema))
  | option (payload : Schema)
  | fixedArray (length : Nat) (element : Schema)
  | boundedArray (capacity : Nat) (element : Schema)
  | boundedBytes (capacity : Nat)
  | boundedString (capacity : Nat)
  deriving Repr, BEq, Inhabited

/-- A source-level route to one scalar in a statically shaped boundary value. This is logical
identity only: it carries no Borsh offset, ABI word, account address, or storage slot. -/
inductive PathStep where
  | field (name : String)
  | tuple (ordinal : Nat)
  | index (ordinal : Nat)
  deriving Repr, BEq, Inhabited

structure StaticLeaf where
  path : Array PathStep
  type : Scalar
  deriving Repr, BEq, Inhabited

/-- One resolved source projection. `partIndex` is interpreted by the target that supplied the
part counts; Core does not assign wire widths, ABI words, or local offsets. -/
structure StaticProjection where
  leafIndex : Nat
  partIndex : Nat
  deriving Repr, BEq, Inhabited

/-- Hard bounds keep user-supplied codec descriptors and generated layouts
finite before a target lowers them. -/
structure Limits where
  maxDepth : Nat := 16
  maxDescriptorNodes : Nat := 1024
  maxLogicalLeaves : Nat := 16384
  maxFields : Nat := 128
  maxVariants : Nat := 128
  maxArrayCapacity : Nat := 4096
  deriving Repr, BEq, Inhabited

structure Usage where
  descriptorNodes : Nat
  logicalLeaves : Nat
  depth : Nat
  deriving Repr, BEq, Inhabited

private def addUsage (left right : Usage) : Usage :=
  { descriptorNodes := left.descriptorNodes + right.descriptorNodes
    logicalLeaves := left.logicalLeaves + right.logicalLeaves
    depth := max left.depth right.depth }

private def scaleUsage (count : Nat) (usage : Usage) : Usage :=
  { descriptorNodes := usage.descriptorNodes
    logicalLeaves := count * usage.logicalLeaves
    depth := usage.depth }

private def namesAreUnique (names : Array String) : Bool :=
  names.all (fun name => !name.isEmpty) && names.toList.eraseDups.length == names.size

private def ensureBudget (limits : Limits) (usage : Usage) : Except String Usage := do
  if usage.descriptorNodes > limits.maxDescriptorNodes then
    throw s!"codec/schema: descriptor nodes exceed {limits.maxDescriptorNodes}"
  if usage.logicalLeaves > limits.maxLogicalLeaves then
    throw s!"codec/schema: logical leaves exceed {limits.maxLogicalLeaves}"
  if usage.depth > limits.maxDepth then
    throw s!"codec/schema: depth exceeds {limits.maxDepth}"
  return usage

private partial def analyzeAt (limits : Limits) (depth : Nat) (schema : Schema) :
    Except String Usage := do
  if depth > limits.maxDepth then
    throw s!"codec/schema: depth exceeds {limits.maxDepth}"
  let usage ← match schema with
    | .unit => pure { descriptorNodes := 1, logicalLeaves := 0, depth }
    | .scalar type =>
        unless type.isWellFormed do
          throw "codec/schema: invalid scalar width"
        pure { descriptorNodes := 1, logicalLeaves := 1, depth }
    | .tuple items =>
        if items.isEmpty then throw "codec/schema: empty tuple"
        let mut usage := { descriptorNodes := 1, logicalLeaves := 0, depth }
        for item in items do
          usage := addUsage usage (← analyzeAt limits (depth + 1) item)
        pure usage
    | .record name fields =>
        if name.isEmpty then throw "codec/schema: empty record name"
        if fields.isEmpty then throw "codec/schema: empty record"
        if fields.size > limits.maxFields then
          throw s!"codec/schema: record fields exceed {limits.maxFields}"
        unless namesAreUnique (fields.map (·.1)) do
          throw "codec/schema: record field names must be non-empty and unique"
        let mut usage := { descriptorNodes := 1, logicalLeaves := 0, depth }
        for field in fields do
          usage := addUsage usage (← analyzeAt limits (depth + 1) field.2)
        pure usage
    | .enumeration name tagBits variants =>
        if name.isEmpty then throw "codec/schema: empty enum name"
        unless tagBits == 8 || tagBits == 16 || tagBits == 32 do
          throw "codec/schema: enum tag must be 8, 16, or 32 bits"
        if variants.isEmpty then throw "codec/schema: empty enum"
        if variants.size > limits.maxVariants then
          throw s!"codec/schema: enum variants exceed {limits.maxVariants}"
        unless namesAreUnique (variants.map (·.1)) do
          throw "codec/schema: enum variant names must be non-empty and unique"
        let mut nodes := 1
        let mut leaves := 1
        let mut maxDepth := depth
        for variant in variants do
          let variantUsage ← analyzeAt limits (depth + 1) variant.2
          nodes := nodes + variantUsage.descriptorNodes
          leaves := max leaves (1 + variantUsage.logicalLeaves)
          maxDepth := max maxDepth variantUsage.depth
        pure { descriptorNodes := nodes, logicalLeaves := leaves, depth := maxDepth }
    | .option payload =>
        let payloadUsage ← analyzeAt limits (depth + 1) payload
        let nodes := 1 + payloadUsage.descriptorNodes
        let leaves := 1 + payloadUsage.logicalLeaves
        pure { descriptorNodes := nodes, logicalLeaves := leaves, depth := payloadUsage.depth }
    | .fixedArray length element =>
        if length == 0 then throw "codec/schema: zero-length fixed array"
        if length > limits.maxArrayCapacity then
          throw s!"codec/schema: array length exceeds {limits.maxArrayCapacity}"
        let elementUsage ← analyzeAt limits (depth + 1) element
        pure (addUsage { descriptorNodes := 1, logicalLeaves := 0, depth }
          (scaleUsage length elementUsage))
    | .boundedArray capacity element =>
        if capacity == 0 then throw "codec/schema: zero-capacity bounded array"
        if capacity > limits.maxArrayCapacity then
          throw s!"codec/schema: array capacity exceeds {limits.maxArrayCapacity}"
        let elementUsage ← analyzeAt limits (depth + 1) element
        let elements := scaleUsage capacity elementUsage
        let nodes := 1 + elements.descriptorNodes
        let leaves := 1 + elements.logicalLeaves
        pure { descriptorNodes := nodes, logicalLeaves := leaves, depth := elements.depth }
    | .boundedBytes capacity | .boundedString capacity =>
        if capacity == 0 then throw "codec/schema: zero-capacity bounded byte sequence"
        if capacity > limits.maxArrayCapacity then
          throw s!"codec/schema: byte capacity exceeds {limits.maxArrayCapacity}"
        pure { descriptorNodes := 2, logicalLeaves := 1 + capacity, depth := depth + 1 }
  ensureBudget limits usage

def analyze (schema : Schema) (limits : Limits := {}) : Except String Usage :=
  analyzeAt limits 1 schema

def validate (schema : Schema) (limits : Limits := {}) : Except String Unit := do
  let _ ← analyze schema limits
  return ()

private partial def staticLeavesAt (path : Array PathStep) : Schema → Except String (Array StaticLeaf)
  | .unit => pure #[]
  | .scalar type => pure #[{ path, type }]
  | .tuple items => do
      let mut leaves := #[]
      for i in [0:items.size] do
        leaves := leaves ++ (← staticLeavesAt (path.push (.tuple i)) items[i]!)
      return leaves
  | .record _ fields => do
      let mut leaves := #[]
      for field in fields do
        leaves := leaves ++ (← staticLeavesAt (path.push (.field field.1)) field.2)
      return leaves
  | .fixedArray length element => do
      let mut leaves := #[]
      for i in [0:length] do
        leaves := leaves ++ (← staticLeavesAt (path.push (.index i)) element)
      return leaves
  | .enumeration .. =>
      throw "codec/schema: static leaf plan requires a target-owned enum tag policy"
  | .option _ =>
      throw "codec/schema: static leaf plan requires a target-owned option tag policy"
  | .boundedArray .. =>
      throw "codec/schema: bounded arrays require a target-owned length policy"
  | .boundedBytes .. | .boundedString .. =>
      throw "codec/schema: bounded bytes and strings require a target-owned length policy"

/-- Flatten only source-order, statically present scalar leaves. Variable/tagged shapes stay
closed until a target explicitly owns their tag/length representation. -/
def staticLeaves (schema : Schema) : Except String (Array StaticLeaf) := do
  let _ ← validate schema
  staticLeavesAt #[] schema

/-- Compatibility spelling used by scalar Ops projections. Extract currently flattens nested
record fields with `_`, binary products as `fst`/`snd`, and fixed indexes as `_0`, `_1`, ... .
The typed `path` remains authoritative; callers must reject ambiguous flattened spellings. -/
def StaticLeaf.sourceName (leaf : StaticLeaf) : String :=
  leaf.path.foldl (init := "") fun out step =>
    match step with
    | .field name => if out.isEmpty then name else out ++ "_" ++ name
    | .tuple 0 => if out.isEmpty then "fst" else out ++ "_fst"
    | .tuple 1 => if out.isEmpty then "snd" else out ++ "_snd"
    | .tuple ordinal => if out.isEmpty then toString ordinal else out ++ "_" ++ toString ordinal
    | .index ordinal => out ++ "_" ++ toString ordinal

/-- Resolve Extract's flattened source spelling against typed static leaves. Targets supply only
the number and spelling of their fixed scalar parts. Exact leaf names are valid for one-part
values; multi-part values require a target-recognized suffix. Ambiguous compatibility names fail
closed rather than selecting the first matching path. -/
def resolveSourceProjection (leaves : Array StaticLeaf) (partCounts : Array Nat)
    (partIndex? : String → Option Nat) (name : String) : Except String StaticProjection := do
  unless partCounts.size == leaves.size do
    throw "codec/schema: static projection part metadata is incomplete"
  let mut found : Array StaticProjection := #[]
  for i in [0:leaves.size] do
    let sourceName := leaves[i]!.sourceName
    let partCount := partCounts[i]!
    if name == sourceName && partCount == 1 then
      found := found.push { leafIndex := i, partIndex := 0 }
    else if !sourceName.isEmpty && name.startsWith (sourceName ++ "_") then
      let suffix := name.drop (sourceName.length + 1) |>.copy
      if let some partIndex := partIndex? suffix then
        if partIndex < partCount then
          found := found.push { leafIndex := i, partIndex }
  unless found.size == 1 do
    throw s!"codec/schema: static projection {name} is missing or ambiguous"
  return found[0]!

end ProofForge.Core.Codec
