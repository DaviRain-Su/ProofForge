import ProofForge.Ops
import ProofForge.Core.Schema

namespace ProofForge.Core

inductive CheckedArith where
  | add | sub | mul | div | mod
  deriving BEq, Repr, Inhabited

/-- A source value or an explicitly named checked calculation; no backend accumulator is observable. -/
inductive ValueRef where
  | source (value : Ops.Val)
  | checked (kind : CheckedArith) (lhs rhs : Ops.Val)
  deriving BEq, Repr, Inhabited

/-- A target-neutral write to one statically known source-level state leaf. -/
structure StateWrite where
  place : Place
  value : ValueRef
  deriving BEq, Repr, Inhabited

/-- A runtime vector index plus a typed path inside one element. -/
structure DynamicPlace where
  vector : Place
  index : Ops.Val
  /-- Relative to the element root; empty for a vector of scalar leaves. -/
  elementPath : Array PathStep := #[]
  deriving BEq, Repr, Inhabited

structure DynamicWrite where
  place : DynamicPlace
  value : ValueRef
  deriving BEq, Repr, Inhabited

/-- Successful completion of a mutating source expression and any accompanying static writes. -/
structure Commit where
  writes : Array StateWrite := #[]
  result : ValueRef
  deriving BEq, Repr, Inhabited

/-- Target-neutral state effects retain source control structure rather than emitter traversal order. -/
inductive StateEvent where
  | letValue (i : Nat) (value : Ops.Val)
  | write (write : StateWrite)
  | dynamicWrite (write : DynamicWrite)
  | commit (commit : Commit)
  | branch (cmp : Ops.Cmp) (lhs rhs : Ops.Val)
      (thenEvents elseEvents : Array StateEvent)
  | loop (bound : Nat) (body : Array StateEvent)
  deriving BEq, Repr, Inhabited

structure Evaluation where
  /-- False only for hand-authored legacy fixtures that predate Core evaluation. -/
  explicit : Bool := false
  events : Array StateEvent := #[]
  deriving BEq, Repr, Inhabited

private partial def StateEvent.collectCommits (event : StateEvent) : Array Commit :=
  match event with
  | StateEvent.commit item => #[item]
  | StateEvent.branch _ _ _ thenEvents elseEvents =>
      thenEvents.flatMap StateEvent.collectCommits ++
        elseEvents.flatMap StateEvent.collectCommits
  | StateEvent.loop _ body => body.flatMap StateEvent.collectCommits
  | StateEvent.letValue .. | StateEvent.write _ | StateEvent.dynamicWrite _ => #[]

def Evaluation.commits (evaluation : Evaluation) : Array Commit :=
  evaluation.events.flatMap StateEvent.collectCommits

private partial def StateEvent.collectDynamicWrites (event : StateEvent) : Array DynamicWrite :=
  match event with
  | StateEvent.dynamicWrite item => #[item]
  | StateEvent.branch _ _ _ thenEvents elseEvents =>
      thenEvents.flatMap StateEvent.collectDynamicWrites ++
        elseEvents.flatMap StateEvent.collectDynamicWrites
  | StateEvent.loop _ body => body.flatMap StateEvent.collectDynamicWrites
  | StateEvent.letValue .. | StateEvent.write _ | StateEvent.commit _ => #[]

def Evaluation.dynamicWrites (evaluation : Evaluation) : Array DynamicWrite :=
  evaluation.events.flatMap StateEvent.collectDynamicWrites

private def firstPlace (schema : Schema) : Except String Place :=
  match schema.leaves[0]? with
  | some leaf => .ok leaf.place
  | none => .error "extract/unsupported: state schema has no leaves"

private def placeByName (schema : Schema) (name : String) : Except String Place :=
  match schema.leafByName? name with
  | some leaf => .ok leaf.place
  | none => .error s!"extract/unsupported: unknown state leaf {name}"

private def checkedValue? (ops : Array Ops.Op) : Option (Option String × ValueRef) :=
  ops.findSome? fun
    | .checkedAddU64 lhs rhs =>
        some ((match lhs with | .field _ name => some name | _ => none), .checked .add lhs rhs)
    | .checkedSubU64 lhs rhs =>
        some ((match lhs with | .field _ name => some name | _ => none), .checked .sub lhs rhs)
    | .checkedMulU64 lhs rhs =>
        some ((match lhs with | .field _ name => some name | _ => none), .checked .mul lhs rhs)
    | .checkedDivU64 lhs rhs =>
        some ((match lhs with | .field _ name => some name | _ => none), .checked .div lhs rhs)
    | .checkedModU64 lhs rhs =>
        some ((match lhs with | .field _ name => some name | _ => none), .checked .mod lhs rhs)
    | _ => none

private def implicitDestination (schema : Schema) (ops : Array Ops.Op)
    (value : Ops.Val) : Except String Place := do
  if let some (name?, _) := checkedValue? ops then
    match name? with
    | some name => return ← placeByName schema name
    | none => pure ()
  match value with
  | .field _ name =>
      if (schema.leafByName? name).isSome then
        placeByName schema name
      else
        firstPlace schema
  | _ => firstPlace schema

private def implicitValue (ops : Array Ops.Op) (value : Ops.Val) : ValueRef :=
  match checkedValue? ops with
  | some (_, checked) => checked
  | none =>
      match value with
      | .field _ _ => .source (.arg 0)
      | _ => .source value

private def commitFor (schema : Schema) (ops : Array Ops.Op)
    (value : Ops.Val) : Except String Commit := do
  -- Explicit stores have their own events. This completion only returns the source result.
  if Ops.hasStoreField ops then
    return { result := .source value }
  -- `indexSet` already carries its dynamic state write; completion returns its decoded source value.
  if Ops.hasIndexSet ops then
    return { result := .source value }
  -- Option construction is a source-level two-leaf write, independent of either target layout.
  if let some (tag, payload) := schema.firstOption? then
    let (tagValue, payloadValue) :=
      match value with
      | .lit 0 => (ValueRef.source (.lit 0), ValueRef.source (.lit 0))
      | .lit n => (ValueRef.source (.lit 1), ValueRef.source (.lit n))
      | other => (ValueRef.source (.lit 1), ValueRef.source other)
    return {
      writes := #[
        { place := tag.place, value := tagValue },
        { place := payload.place, value := payloadValue }
      ]
      result := payloadValue
    }
  let place ← implicitDestination schema ops value
  let stored := implicitValue ops value
  return { writes := #[{ place, value := stored }], result := stored }

private def dynamicPlace (schema : Schema) (name : String) (index : Ops.Val)
    (byteOffset : Nat) : Except String DynamicPlace := do
  let some vector := schema.vector? name
    | throw s!"extract/unsupported: unknown vector {name}"
  let mut offset := 0
  for leaf in schema.vectorElementLeaves vector do
    if offset == byteOffset then
      let relative := leaf.place.steps.extract (vector.place.steps.size + 1)
      return { vector := vector.place, index, elementPath := relative }
    offset := offset + leaf.width
  throw s!"extract/unsupported: vector {name} has no leaf at byte offset {byteOffset}"

private partial def eventsFor (schema : Schema) (ops : Array Ops.Op) :
    Except String (Array StateEvent) := do
  let mut events := #[]
  for op in ops do
    match op with
    | .letLocal i value =>
        events := events.push (.letValue i value)
    | .ite cmp lhs rhs thenOps elseOps =>
        let thenEvents ← eventsFor schema thenOps
        let elseEvents ← eventsFor schema elseOps
        if !thenEvents.isEmpty || !elseEvents.isEmpty then
          events := events.push (.branch cmp lhs rhs thenEvents elseEvents)
    | .forBody bound body =>
        let bodyEvents ← eventsFor schema body
        if !bodyEvents.isEmpty then
          events := events.push (.loop bound bodyEvents)
    | .indexSet name index value _ byteOffset =>
        let place ← dynamicPlace schema name index byteOffset
        events := events.push (.dynamicWrite { place, value := .source value })
    | .storeField name value =>
        let place ← placeByName schema name
        events := events.push (.write { place, value := .source value })
    | .okState value =>
        events := events.push (.commit (← commitFor schema ops value))
    | _ => pure ()
  return events

/-- Resolve legacy implicit mutation conventions once, before either target backend sees the method. -/
def evaluate (schema : Schema) (ops : Array Ops.Op) : Except String Evaluation := do
  if schema.isEmpty then
    throw "extract/unsupported: Core evaluation requires a typed state schema"
  return { explicit := true, events := ← eventsFor schema ops }

end ProofForge.Core
