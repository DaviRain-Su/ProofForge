import ProofForge.Core.Eval
import ProofForge.Core.Codec

namespace ProofForge.Core.IR

inductive MethodKind where
  | init
  | increment
  | get
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Target-independent method metadata parameterized by one source dialect. -/
structure Method (ValExt : Type) (OpExt : Type → Type) where
  kind : MethodKind
  name : String
  /-- On-chain instruction name. Lean `init` maps to `initialize`. -/
  ixName : String := ""
  paramCount : Nat := 0
  paramWidths : Array Nat := #[]
  /-- Logical boundary types. `paramWidths` remains only for legacy artifacts. -/
  paramTypes : Array Core.Codec.Scalar := #[]
  /-- Target-neutral source shapes, one per public parameter. Targets own their physical layouts. -/
  paramSchemas : Array Core.Codec.Schema := #[]
  /-- Legacy return carrier widths. New target code consumes `retTypes`. -/
  retWidths : Array Nat := #[]
  /-- Logical return types. `retWidths` remains only for legacy artifacts. -/
  retTypes : Array Core.Codec.Scalar := #[]
  /-- Logical public result after removing persisted State and effect wrappers. -/
  retSchema : Core.Codec.Schema := .unit
  retCount : Nat := 1
  /-- Opaque compile-time annotations consumed only by the owning target. They are metadata, not
  executable Ops; foreign targets must either ignore or explicitly reject unknown entries. -/
  annotations : Array String := #[]
  sketch : Array String := #[]
  ops : Array (Core.Ops.Op ValExt OpExt) := #[]
  evaluation : Core.Evaluation ValExt := {}
  deriving Inhabited

/-- A target-neutral logical state slot. Physical offsets belong to target IRs. -/
structure Slot where
  name : String
  width : Nat := 8
  abi : String := "u64-le"
  deriving BEq, Repr, Inhabited

/-- Source program metadata and control flow, independent of any concrete target. -/
structure Program (ValExt : Type) (OpExt : Type → Type) where
  name : String
  slots : Array Slot := #[{ name := "value" }]
  schema : Core.Schema := {}
  methods : Array (Method ValExt OpExt)
  deriving Inhabited

def Program.fields (p : Program ValExt OpExt) : Array String :=
  p.slots.map (·.name)

def slotsOfSchema (schema : Core.Schema) : Array Slot :=
  schema.leaves.map fun leaf =>
    { name := leaf.name, width := leaf.width, abi := leaf.abi }

def schemaMatchesSlots (p : Program ValExt OpExt) : Bool :=
  p.schema.isEmpty || slotsOfSchema p.schema == p.slots

def hasKind (p : Program ValExt OpExt) (kind : MethodKind) : Bool :=
  p.methods.any (·.kind == kind)

def isProgramShape (p : Program ValExt OpExt) : Bool :=
  hasKind p .init && hasKind p .increment && hasKind p .get

def isCounterShape (p : Program ValExt OpExt) : Bool :=
  isProgramShape p

def fieldWidth (p : Program ValExt OpExt) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.width)

def optionLeafNames? (p : Program ValExt OpExt) : Option (String × String) :=
  match p.schema.firstOption? with
  | some (tag, payload) => some (tag.name, payload.name)
  | none => do
      let tag ← p.slots.find? (fun slot => slot.name.endsWith "_tag")
      let payload ← p.slots.find? (fun slot => slot.name.endsWith "_p0")
      return (tag.name, payload.name)

def hasOptionLeaves (p : Program ValExt OpExt) : Bool :=
  (optionLeafNames? p).isSome

/-- Lean declaration suffix to on-chain name. -/
def ixNameOfLean (lean : String) : String :=
  if lean == "init" then "initialize" else lean

def lastName (name : String) : String :=
  match name.splitOn "." with
  | [] => name
  | parts => parts.getLast!

def defaultParamCount : MethodKind → Nat
  | .get => 0
  | _ => 1

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n + 87)

def u64Hex (n : UInt64) : String :=
  let rec go (fuel : Nat) (value : Nat) (acc : String) : String :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
        if value = 0 && acc ≠ "" then acc
        else go fuel' (value / 16) (String.singleton (hexDigit (value % 16)) ++ acc)
  let result := go 17 n.toNat ""
  if result = "" then "0" else result

private def fnvOffset : UInt64 := 14695981039346656037
private def fnvPrime : UInt64 := 1099511628211

def fnv1a64 (value : String) : UInt64 :=
  value.toUTF8.data.foldl (init := fnvOffset) fun hash byte =>
    (hash ^^^ byte.toUInt64) * fnvPrime

/-- Empty-op fixture useful when testing target-independent metadata. -/
def counterProgram {ValExt : Type} {OpExt : Type → Type}
    (name : String := "Counter") : Program ValExt OpExt :=
  { name
    slots := #[{ name := "value" }]
    methods := #[
      { kind := .init, name := "init", ixName := "initialize", paramCount := 1 },
      { kind := .increment, name := "increment", ixName := "increment", paramCount := 1 },
      { kind := .get, name := "get", ixName := "get", paramCount := 0 }
    ] }

end ProofForge.Core.IR
