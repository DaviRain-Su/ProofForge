namespace ProofForge.Core

/-- Core storage leaves keep their source-level scalar identity. Physical target layout is derived later. -/
inductive ScalarTy where
  | uint (bits : Nat)
  | bool
  | enum (typeName : String)
  /-- A one-constructor source inductive whose sole payload is an unsigned scalar. -/
  | newtype (typeName : String) (bits : Nat)
  /-- Discriminant for a fixed-layout multi-constructor source inductive. -/
  | variantTag (typeName : String)
  | optionTag
  deriving BEq, Repr, Inhabited

def ScalarTy.width : ScalarTy → Nat
  | .uint bits => bits / 8
  | .bool => 1
  | .newtype _ bits => bits / 8
  | .enum _ | .variantTag _ | .optionTag => 8

def ScalarTy.abi : ScalarTy → String
  | .uint bits => s!"u{bits}-le"
  | .bool => "u8-le"
  | .newtype _ bits => s!"u{bits}-le"
  | .enum _ | .variantTag _ | .optionTag => "u64-le"

/-- A field is identified by its owner and declaration ordinal; names support diagnostics/compatibility only. -/
inductive PathStep where
  | field (owner : String) (ordinal : Nat) (name : String)
  | index (ordinal : Nat)
  | optionTag
  | optionPayload
  | variantTag
  | variantPayload (ordinal : Nat)
  deriving Repr, Inhabited

instance : BEq PathStep where
  beq left right :=
    match left, right with
    | .field leftOwner leftOrdinal _, .field rightOwner rightOrdinal _ =>
        leftOwner == rightOwner && leftOrdinal == rightOrdinal
    | .index leftOrdinal, .index rightOrdinal => leftOrdinal == rightOrdinal
    | .optionTag, .optionTag | .optionPayload, .optionPayload => true
    | .variantTag, .variantTag => true
    | .variantPayload left, .variantPayload right => left == right
    | _, _ => false

/-- Stable source-level identity for a state location. No byte offset or target storage slot lives here. -/
structure Place where
  steps : Array PathStep := #[]
  deriving BEq, Repr, Inhabited

def Place.push (p : Place) (step : PathStep) : Place :=
  { steps := p.steps.push step }

def Place.isPrefixOf (head place : Place) : Bool :=
  head.steps.toList.isPrefixOf place.steps.toList

structure Leaf where
  place : Place
  /-- Compatibility/display name. Identity is `place`, not this flattened spelling. -/
  name : String
  ty : ScalarTy
  deriving BEq, Repr, Inhabited

def Leaf.width (leaf : Leaf) : Nat :=
  leaf.ty.width

def Leaf.abi (leaf : Leaf) : String :=
  leaf.ty.abi

/-- Target-neutral facts about a fixed-length vector. -/
structure VectorLayout where
  place : Place
  /-- Compatibility/display name used while legacy Ops still refer to vectors by name. -/
  name : String
  length : Nat
  elementBytes : Nat
  elementLeaves : Nat
  deriving BEq, Repr, Inhabited

/-- Typed state schema produced from the `init` result type before Ops extraction. -/
structure Schema where
  rootType : String := ""
  leaves : Array Leaf := #[]
  vectors : Array VectorLayout := #[]
  deriving BEq, Repr, Inhabited

def Schema.isEmpty (schema : Schema) : Bool :=
  schema.rootType.isEmpty && schema.leaves.isEmpty

def Schema.leafByName? (schema : Schema) (name : String) : Option Leaf :=
  schema.leaves.find? (·.name == name)

def Schema.leafAt? (schema : Schema) (place : Place) : Option Leaf :=
  schema.leaves.find? (·.place == place)

def Schema.leafName? (schema : Schema) (place : Place) : Option String :=
  (schema.leafAt? place).map (·.name)

def Schema.vector? (schema : Schema) (name : String) : Option VectorLayout :=
  schema.vectors.find? (·.name == name)

def Schema.vectorBaseLeafIndex? (schema : Schema) (vector : VectorLayout) : Option Nat :=
  schema.leaves.findIdx? fun leaf => vector.place.isPrefixOf leaf.place

private def lastStep? (place : Place) : Option PathStep :=
  place.steps[place.steps.size - 1]?

private def sameOptionParent (tag payload : Place) : Bool :=
  tag.steps.pop == payload.steps.pop

/-- First Option tag/payload pair in declaration order. Current Ops supports one implicit Option writeback. -/
def Schema.firstOption? (schema : Schema) : Option (Leaf × Leaf) := do
  let tag ← schema.leaves.find? fun leaf => lastStep? leaf.place == some .optionTag
  let payload ← schema.leaves.find? fun leaf =>
    lastStep? leaf.place == some .optionPayload && sameOptionParent tag.place leaf.place
  return (tag, payload)

def Schema.hasOption (schema : Schema) : Bool :=
  schema.firstOption?.isSome

/-- Leaves of element zero, in physical declaration order. -/
def Schema.vectorElementLeaves (schema : Schema) (vector : VectorLayout) : Array Leaf :=
  match schema.vectorBaseLeafIndex? vector with
  | none => #[]
  | some first => schema.leaves.extract first (first + vector.elementLeaves)

private def relativeStepName : PathStep → Option String
  | .field _ _ name => some name
  | .optionTag => some "tag"
  | .optionPayload => some "p0"
  | .variantTag => some "tag"
  | .variantPayload ordinal => some s!"p{ordinal}"
  | .index _ => none

/-- Logical leaf path inside one vector element (`nodes[i].value` → `value`). -/
def VectorLayout.relativeLeafName (vector : VectorLayout) (leaf : Leaf) : String :=
  let relative := leaf.place.steps.extract vector.place.steps.size
  let names := relative.filterMap relativeStepName
  String.intercalate "_" names.toList

end ProofForge.Core
