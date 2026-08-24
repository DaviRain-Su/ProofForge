import ProofForge.Extract.IR
import ProofForge.Evm.Ops
import ProofForge.Crypto.Keccak

namespace ProofForge.Evm.IR

open ProofForge.Crypto

/-- EVM instructions are owned by the EVM lowering boundary, not by the frontend Ops enum. -/
inductive Op where
  | letLocal (i : Nat) (value : Ops.Val)
  | joinLocal (i : Nat)
  | setLocal (i : Nat) (value : Ops.Val)
  | checkedAddU64 (lhs rhs : Ops.Val)
  | checkedSubU64 (lhs rhs : Ops.Val)
  | checkedMulU64 (lhs rhs : Ops.Val)
  | checkedDivU64 (lhs rhs : Ops.Val)
  | checkedModU64 (lhs rhs : Ops.Val)
  | ite (cmp : Ops.Cmp) (lhs rhs : Ops.Val) (thn els : Array Op)
  | evmDeposit (amount : Ops.Val)
  | evmSendEth (w0 w1 w2 amount : Ops.Val)
  | evmLog (name : String) (amount : Ops.Val)
  | forAccum (n : Nat) (addend : Ops.Val)
  | forBody (n : Nat) (body : Array Op)
  | indexSet (name : String) (idx value : Ops.Val) (len : Nat) (elemOff : Nat := 0)
  | mapGetU64 (base key : Ops.Val)
  | mapSetU64 (base key value : Ops.Val)
  | mapGetAddr (base w0 w1 w2 : Ops.Val)
  | mapSetAddr (base w0 w1 w2 value : Ops.Val)
  | mapGetPair (base o0 o1 o2 s0 s1 s2 : Ops.Val)
  | mapSetPair (base o0 o1 o2 s0 s1 s2 value : Ops.Val)
  | evmTokenTransfer (tw0 tw1 tw2 dw0 dw1 dw2 amount : Ops.Val)
  | evmTokenBalanceOfSelf (tw0 tw1 tw2 : Ops.Val)
  | storeField (name : String) (value : Ops.Val)
  | okState (value : Ops.Val)
  | errorOverflow
  | errorNamed (name : String)
  | returnU64 (value : Ops.Val)
  | returnState (value : Ops.Val)
  deriving BEq, Repr, Inhabited

private partial def lowerOp : Ops.Op → Except String Op
  | .letLocal i value => pure (.letLocal i value)
  | .joinLocal i => pure (.joinLocal i)
  | .setLocal i value => pure (.setLocal i value)
  | .checkedAddU64 lhs rhs => pure (.checkedAddU64 lhs rhs)
  | .checkedSubU64 lhs rhs => pure (.checkedSubU64 lhs rhs)
  | .checkedMulU64 lhs rhs => pure (.checkedMulU64 lhs rhs)
  | .checkedDivU64 lhs rhs => pure (.checkedDivU64 lhs rhs)
  | .checkedModU64 lhs rhs => pure (.checkedModU64 lhs rhs)
  | .ite cmp lhs rhs thn els =>
      return .ite cmp lhs rhs (← lowerOps thn) (← lowerOps els)
  | .forAccum n addend => pure (.forAccum n addend)
  | .forBody n body => return .forBody n (← lowerOps body)
  | .indexSet name idx value len elemOff => pure (.indexSet name idx value len elemOff)
  | .storeField name value => pure (.storeField name value)
  | .okState value => pure (.okState value)
  | .errorOverflow => pure .errorOverflow
  | .errorNamed name => pure (.errorNamed name)
  | .returnU64 value => pure (.returnU64 value)
  | .returnState value => pure (.returnState value)
  | .ext (.deposit amount) => pure (.evmDeposit amount)
  | .ext (.sendEth w0 w1 w2 amount) => pure (.evmSendEth w0 w1 w2 amount)
  | .ext (.log name amount) => pure (.evmLog name amount)
  | .ext (.mapGetU64 base key) => pure (.mapGetU64 base key)
  | .ext (.mapSetU64 base key value) => pure (.mapSetU64 base key value)
  | .ext (.mapGetAddr base w0 w1 w2) => pure (.mapGetAddr base w0 w1 w2)
  | .ext (.mapSetAddr base w0 w1 w2 value) => pure (.mapSetAddr base w0 w1 w2 value)
  | .ext (.mapGetPair base o0 o1 o2 s0 s1 s2) =>
      pure (.mapGetPair base o0 o1 o2 s0 s1 s2)
  | .ext (.mapSetPair base o0 o1 o2 s0 s1 s2 value) =>
      pure (.mapSetPair base o0 o1 o2 s0 s1 s2 value)
  | .ext (.tokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount) =>
      pure (.evmTokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount)
  | .ext (.tokenBalanceOfSelf tw0 tw1 tw2) =>
      pure (.evmTokenBalanceOfSelf tw0 tw1 tw2)

where
  lowerOps (ops : Array Ops.Op) : Except String (Array Op) :=
    ops.mapM lowerOp

def ofSourceOps (ops : Array Ops.Op) : Except String (Array Op) :=
  ops.mapM lowerOp

private partial def walk (fuel : Nat) (ops : Array Op) (predicate : Op → Bool) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
      ops.any fun op =>
        predicate op ||
          match op with
          | .ite _ _ _ thn els => walk fuel' thn predicate || walk fuel' els predicate
          | .forBody _ body => walk fuel' body predicate
          | _ => false

def hasStoreField (ops : Array Op) : Bool :=
  walk 16 ops fun | .storeField .. => true | _ => false

def hasIndexSet (ops : Array Op) : Bool :=
  walk 16 ops fun | .indexSet .. => true | _ => false

def hasCheckedArith (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
    | .checkedDivU64 .. | .checkedModU64 .. => true
    | _ => false

def hasEvmDeposit (ops : Array Op) : Bool :=
  walk 16 ops fun | .evmDeposit _ => true | _ => false

structure Slot where
  place : Option Core.Place := none
  name : String
  index : Nat
  /-- 物理宽：1/2/4/8。EVM 仍占一个 storage word，窄值在低字节。 -/
  width : Nat := 8
  deriving BEq, Repr, Inhabited

structure VectorLeaf where
  elementPath : Array Core.PathStep := #[]
  byteOffset : Nat
  slotOffset : Nat
  width : Nat
  deriving BEq, Repr, Inhabited

/-- Physical EVM storage layout for a fixed-length source vector. -/
structure Vector where
  place : Option Core.Place := none
  name : String
  baseSlot : Nat
  length : Nat
  strideSlots : Nat
  leaves : Array VectorLeaf := #[]
  deriving BEq, Repr, Inhabited

structure Method where
  kind : Core.IR.MethodKind
  name : String
  ixName : String
  selector : String := ""
  paramCount : Nat := 0
  paramWidths : Array Nat := #[]
  retCount : Nat := 1
  ops : Array Op := #[]
  evaluation : Core.Evaluation Ops.ValKind := {}
  view : Bool := false
  payable : Bool := false
  deriving BEq, Repr, Inhabited

structure Program where
  name : String
  slots : Array Slot
  vectors : Array Vector := #[]
  /-- Target-neutral source identity retained across EVM lowering. -/
  schema : Core.Schema := {}
  constructor : Method
  entries : Array Method
  deriving BEq, Repr, Inhabited

def slotIndex (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.index)

def slotWidth (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.width)

def optionLeafNames? (p : Program) : Option (String × String) :=
  match p.schema.firstOption? with
  | some (tag, payload) => some (tag.name, payload.name)
  | none => do
      let tag ← p.slots.find? (fun slot => slot.name.endsWith "_tag")
      let payload ← p.slots.find? (fun slot => slot.name.endsWith "_p0")
      return (tag.name, payload.name)

def hasOptionLeaves (p : Program) : Bool :=
  (optionLeafNames? p).isSome

private def legacyVector (p : Program) (name : String) : Option Vector :=
  let pre0 := name ++ "_0"
  let group :=
    p.slots.filter fun slot => slot.name == pre0 || slot.name.startsWith (pre0 ++ "_")
  if group.isEmpty then none
  else
    let digitPrefix (value : String) : String :=
      Id.run do
        let mut out := ""
        for c in value.toList do
          if c.isDigit then out := out.push c else return out
        return out
    let length :=
      p.slots.foldl (init := 0) fun acc slot =>
        let rest :=
          if slot.name.startsWith (name ++ "_") then
            digitPrefix (slot.name.drop (name.length + 1) |>.copy)
          else ""
        match rest.toNat? with
        | some i => Nat.max acc (i + 1)
        | none => acc
    let baseSlot := group[0]!.index
    if length == 0 then none
    else some { name, baseSlot, length, strideSlots := group.size }

def vector? (p : Program) (name : String) : Option Vector :=
  match p.vectors.find? (·.name == name) with
  | some vector => some vector
  | none => legacyVector p name

def vectorBaseSlot (p : Program) (name : String) : Option Nat :=
  (vector? p name).map (·.baseSlot)

def vectorLenOf (p : Program) (name : String) (given : Nat) : Nat :=
  if given != 0 then given else (vector? p name).map (·.length) |>.getD 0

def vectorStrideSlots (p : Program) (name : String) : Nat :=
  (vector? p name).map (·.strideSlots) |>.getD 1

/-- Convert a byte offset within one source vector element to its EVM leaf-slot offset. -/
def vectorLeafSlotOffset (p : Program) (name : String) (byteOffset : Nat) : Nat :=
  match p.vectors.find? (·.name == name) with
  | some vector =>
      (vector.leaves.find? (·.byteOffset == byteOffset)).map (·.slotOffset)
        |>.getD vector.leaves.size
  | none => byteOffset / 8

/-- Width of the leaf at one byte offset within a source vector element. -/
def vectorLeafWidth (p : Program) (name : String) (byteOffset : Nat) : Option Nat := do
  let vector ← vector? p name
  if vector.leaves.isEmpty then
    -- Legacy fixtures only model vectors of UInt64 leaves.
    some 8
  else
    (vector.leaves.find? (·.byteOffset == byteOffset)).map (·.width)

private def rejectSlot (slot : Core.IR.Slot) : Option String :=
  if !(slot.width == 1 || slot.width == 2 || slot.width == 4 || slot.width == 8) then
    some s!"extract/unsupported: evm slot {slot.name} width {slot.width}"
  else none

private def isCtor (method : Extract.IR.Method) : Bool :=
  method.kind == .init

private def lowerVectors (src : Extract.IR.Program) (slots : Array Slot) : Array Vector :=
  src.schema.vectors.filterMap fun vector => do
    let baseSlot ← src.schema.vectorBaseLeafIndex? vector
    let _ ← slots[baseSlot]?
    let sourceLeaves := src.schema.vectorElementLeaves vector
    let leaves := sourceLeaves.mapIdx fun slotOffset leaf =>
      let byteOffset := (sourceLeaves.extract 0 slotOffset).foldl (init := 0) fun n item =>
        n + item.width
      ({
        elementPath := leaf.place.steps.extract (vector.place.steps.size + 1)
        byteOffset
        slotOffset
        width := leaf.width
      } : VectorLeaf)
    return {
      place := some vector.place
      name := vector.name
      baseSlot
      length := vector.length
      strideSlots := vector.elementLeaves
      leaves
    }

private def lowerMethodBody (schema : Core.Schema) (method : Extract.IR.Method) :
    Except String (Array Op × Core.Evaluation Ops.ValKind) := do
  let sourceOps ← Extract.IR.toEvmOps method.ops
  unless sourceOps.all Ops.Op.wellFormed do
    throw s!"extract/ir: malformed EVM Ops in {method.ixName}"
  let evaluation ←
    if schema.isEmpty then pure {}
    else Core.evaluate schema sourceOps
  return (← ofSourceOps sourceOps, evaluation)

/-- Project the combined extractor dialect and lower it into an EVM-owned physical program. -/
def fromExtracted (src : Extract.IR.Program) : Except String Program := do
  src.validateEvm
  if src.slots.isEmpty then
    throw "extract/unsupported: evm program has no slots"
  for slot in src.slots do
    if let some reason := rejectSlot slot then
      throw reason
  let mut ctors : Array Extract.IR.Method := #[]
  let mut extras : Array Extract.IR.Method := #[]
  for method in src.methods do
    if isCtor method then
      ctors := ctors.push method
    else
      extras := extras.push method
  if ctors.isEmpty then
    throw "extract/unsupported: evm wants a constructor"
  let ctorSrc :=
    match ctors.find? (fun m =>
        m.ixName == "initialize" || Core.IR.lastName m.name == "init") with
    | some m => m
    | none => ctors[0]!
  -- EVM initialization is deployment-only. Alternative source initializers may remain useful to
  -- targets such as SVM, but exposing them as runtime selectors would allow storage reinitialization.
  let rest := extras
  if rest.isEmpty then
    throw "extract/unsupported: evm wants at least one entry"
  if ctorSrc.ops.isEmpty then
    throw "extract/unsupported: init missing returnState"
  unless ctorSrc.ops.any (fun | .returnState _ => true | _ => false) do
    throw "extract/unsupported: init missing returnState"
  let (ctorOps, ctorEvaluation) ← lowerMethodBody src.schema ctorSrc
  let ctor : Method := {
    kind := ctorSrc.kind
    name := ctorSrc.name
    ixName := ctorSrc.ixName
    selector := ""
    paramCount := ctorSrc.paramCount
    paramWidths := ctorSrc.paramWidths
    retCount := 1
    ops := ctorOps
    evaluation := ctorEvaluation
    view := false
    payable := false
  }
  let mut entries : Array Method := #[]
  for m in rest do
    if m.ops.isEmpty then
      throw s!"extract/unsupported: empty ops {m.ixName}"
    let widths :=
      if m.paramWidths.size == m.paramCount then m.paramWidths
      else Array.replicate m.paramCount 8
    let sel := Keccak.selectorOfWidths m.ixName widths
    let view := m.kind == .get
    let (ops, evaluation) ← lowerMethodBody src.schema m
    entries := entries.push {
      kind := m.kind
      name := m.name
      ixName := m.ixName
      selector := sel
      paramCount := m.paramCount
      paramWidths := widths
      retCount := m.retCount
      ops
      evaluation
      view
      payable := !view && hasEvmDeposit ops
    }
  let slots := src.slots.mapIdx fun i s =>
    { place := (src.schema.leaves[i]?).map (·.place), name := s.name, index := i, width := s.width }
  return {
    name := src.name
    slots
    vectors := lowerVectors src slots
    schema := src.schema
    constructor := ctor
    entries
  }

private def cmpTag : Ops.Cmp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt"
  | .le => "le" | .gt => "gt" | .ge => "ge"

/-- Preserve the old closed-union spelling in canonical digests during the IR migration. -/
private def legacyCmpRepr (cmp : Ops.Cmp) : String :=
  "ProofForge.Ops.Cmp." ++ cmpTag cmp

private partial def valCanon : Ops.Val → String
  | .arg i => s!"a{i}"
  | .local i => s!"v{i}"
  | .lit n => s!"l{n.toNat}"
  | .field b n => s!"f.{n}({valCanon b})"
  | .ext .caller #[] => "ecall"
  | .ext .blockNumber #[] => "eblk"
  | .ext .timestamp #[] => "ets"
  | .ext .chainId #[] => "echain"
  | .ext .self #[] => "eself"
  | .ext .callValue #[] => "eval"
  | .ext .selfBalance #[] => "ebal"
  | .ext .callerW0 #[] => "ecw0"
  | .ext .callerW1 #[] => "ecw1"
  | .ext .callerW2 #[] => "ecw2"
  | .ext .selfW0 #[] => "esw0"
  | .ext .selfW1 #[] => "esw1"
  | .ext .selfW2 #[] => "esw2"
  | .bitAnd l r => s!"and({valCanon l},{valCanon r})"
  | .bitOr l r => s!"or({valCanon l},{valCanon r})"
  | .bitXor l r => s!"xor({valCanon l},{valCanon r})"
  | .bitNot v => s!"not({valCanon v})"
  | .shiftL l r => s!"shl({valCanon l},{valCanon r})"
  | .shiftR l r => s!"shr({valCanon l},{valCanon r})"
  | .indexGet b n i k off =>
      if off == 0 then s!"idx.{n}[{valCanon i}/{k}]({valCanon b})"
      else s!"idx.{n}+{off}[{valCanon i}/{k}]({valCanon b})"
  | .loopIx => "ix"
  | .select c l r t f =>
      s!"sel.{legacyCmpRepr c}({valCanon l},{valCanon r},{valCanon t},{valCanon f})"
  | .addU64 l r => s!"uadd({valCanon l},{valCanon r})"
  | .subU64 l r => s!"usub({valCanon l},{valCanon r})"
  | .mulU64 l r => s!"umul({valCanon l},{valCanon r})"
  | .divU64 l r => s!"udiv({valCanon l},{valCanon r})"
  | .modU64 l r => s!"umod({valCanon l},{valCanon r})"
  | .ext .mapGetU64 #[b, k] => s!"vg({valCanon b},{valCanon k})"
  | .ext .mapGetAddr #[b, a0, a1, a2] =>
      s!"vga({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2})"
  | .ext .mapGetPair #[b, a0, a1, a2, c0, c1, c2] =>
      s!"vgp({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2},{valCanon c0},{valCanon c1},{valCanon c2})"
  | .ext kind operands =>
      s!"ext.{repr kind}({String.intercalate "," (operands.map valCanon).toList})"

private partial def opsCanon (ops : Array Op) : String :=
  let rec one (op : Op) : String :=
    match op with
    | .letLocal i v => s!"let.{i}({valCanon v})"
    | .joinLocal i => s!"join.{i}"
    | .setLocal i v => s!"set.{i}({valCanon v})"
    | .checkedAddU64 l r => s!"add({valCanon l},{valCanon r})"
    | .checkedSubU64 l r => s!"sub({valCanon l},{valCanon r})"
    | .checkedMulU64 l r => s!"mul({valCanon l},{valCanon r})"
    | .checkedDivU64 l r => s!"div({valCanon l},{valCanon r})"
    | .checkedModU64 l r => s!"mod({valCanon l},{valCanon r})"
    | .ite c l r t f => s!"ite.{cmpTag c}({valCanon l},{valCanon r},[{opsCanon t}],[{opsCanon f}])"
    | .evmDeposit v => s!"edep({valCanon v})"
    | .evmSendEth a b c d =>
        s!"esend({valCanon a},{valCanon b},{valCanon c},{valCanon d})"
    | .evmLog n v => s!"elog.{n}({valCanon v})"
    | .forAccum n v => s!"for({n},{valCanon v})"
    | .forBody n body => s!"forb({n},[{opsCanon body}])"
    | .indexSet n i v k off =>
        if off == 0 then s!"iset.{n}[{valCanon i}/{k}]({valCanon v})"
        else s!"iset.{n}+{off}[{valCanon i}/{k}]({valCanon v})"
    | .mapGetU64 b k => s!"mget({valCanon b},{valCanon k})"
    | .mapSetU64 b k v => s!"mset({valCanon b},{valCanon k},{valCanon v})"
    | .mapGetAddr b a0 a1 a2 =>
        s!"mgeta({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2})"
    | .mapSetAddr b a0 a1 a2 v =>
        s!"mseta({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2},{valCanon v})"
    | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
        s!"mgetp({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2},{valCanon c0},{valCanon c1},{valCanon c2})"
    | .mapSetPair b a0 a1 a2 c0 c1 c2 v =>
        s!"msetp({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2},{valCanon c0},{valCanon c1},{valCanon c2},{valCanon v})"
    | .evmTokenTransfer a b c d e f g =>
        s!"ttxfer({valCanon a},{valCanon b},{valCanon c},{valCanon d},{valCanon e},{valCanon f},{valCanon g})"
    | .evmTokenBalanceOfSelf a b c =>
        s!"tbal({valCanon a},{valCanon b},{valCanon c})"
    | .storeField n v => s!"st.{n}({valCanon v})"
    | .okState v => s!"ok({valCanon v})"
    | .errorOverflow => "ovf"
    | .errorNamed n => s!"err.{n}"
    | .returnU64 v => s!"retu({valCanon v})"
    | .returnState v => s!"rets({valCanon v})"
  String.intercalate ";" (ops.toList.map one)

def canonical (p : Program) : String :=
  let slots := String.intercalate ","
    (p.slots.map (fun s => s!"{s.name}:{s.width}")).toList
  let ctor := s!"ctor:{p.constructor.paramCount}:[{opsCanon p.constructor.ops}]"
  let entries :=
    (p.entries.qsort (fun a b => a.ixName < b.ixName)).toList.map fun m =>
      let tag := if m.view then "view" else if m.payable then "pay" else "mut"
      let base := s!"{tag}:{m.ixName}:{m.selector}:{m.paramCount}:[{opsCanon m.ops}]"
      if (m.paramWidths.isEmpty || m.paramWidths.all (· == 8)) && m.retCount == 1 then
        base
      else
        let widths := String.intercalate "," (m.paramWidths.map toString).toList
        s!"{tag}:{m.ixName}:{m.selector}:{m.paramCount}:{widths}:r{m.retCount}:[{opsCanon m.ops}]"
  s!"evm|{p.name}|{slots}|{ctor}|{String.intercalate "/" entries}"

def digestHex (p : Program) : String :=
  Core.IR.u64Hex (Core.IR.fnv1a64 (canonical p))

end ProofForge.Evm.IR
