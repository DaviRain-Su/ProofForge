import ProofForge.Extract.IR
import ProofForge.Svm.ABI

namespace ProofForge.Svm.IR

/-- SVM instructions are lowered separately from the target-owned source Ops. -/
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
  | invoke (programIx : Nat) (metas : Array Ops.CpiMeta)
      (data : Array (Ops.CpiWord Ops.Val))
      (seeds : Array Ops.PdaSeed := #[]) (bump : Option Ops.Val := none)
  | forAccum (n : Nat) (addend : Ops.Val) (resultLocal : Nat)
  | forBody (n : Nat) (body : Array Op)
  | indexSet (name : String) (idx value : Ops.Val) (len : Nat) (elemOff : Nat := 0)
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
  | .ext (.invoke programIx metas data seed bump) =>
      pure (.invoke programIx metas data seed bump)
  | .forAccum n addend resultLocal => pure (.forAccum n addend resultLocal)
  | .forBody n body => return .forBody n (← lowerOps body)
  | .indexSetLeaf name _ _ _ leaf =>
      throw s!"extract/ir: unresolved vector leaf {name}.{leaf}"
  | .indexSet name idx value len elemOff => pure (.indexSet name idx value len elemOff)
  | .storeField name value => pure (.storeField name value)
  | .okState value => pure (.okState value)
  | .errorOverflow => pure .errorOverflow
  | .errorNamed name => pure (.errorNamed name)
  | .returnU64 value => pure (.returnU64 value)
  | .returnState value => pure (.returnState value)

where
  lowerOps (ops : Array Ops.Op) : Except String (Array Op) :=
    ops.mapM lowerOp

def ofSourceOps (ops : Array Ops.Op) : Except String (Array Op) :=
  ops.mapM lowerOp

private partial def Op.toSource : Op → Ops.Op
  | .letLocal i value => .letLocal i value
  | .joinLocal i => .joinLocal i
  | .setLocal i value => .setLocal i value
  | .checkedAddU64 lhs rhs => .checkedAddU64 lhs rhs
  | .checkedSubU64 lhs rhs => .checkedSubU64 lhs rhs
  | .checkedMulU64 lhs rhs => .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs => .checkedDivU64 lhs rhs
  | .checkedModU64 lhs rhs => .checkedModU64 lhs rhs
  | .ite cmp lhs rhs thn els => .ite cmp lhs rhs (toSourceOps thn) (toSourceOps els)
  | .invoke programIx metas data seed bump => .ext (.invoke programIx metas data seed bump)
  | .forAccum n addend resultLocal => .forAccum n addend resultLocal
  | .forBody n body => .forBody n (toSourceOps body)
  | .indexSet name idx value len elemOff => .indexSet name idx value len elemOff
  | .storeField name value => .storeField name value
  | .okState value => .okState value
  | .errorOverflow => .errorOverflow
  | .errorNamed name => .errorNamed name
  | .returnU64 value => .returnU64 value
  | .returnState value => .returnState value

where
  toSourceOps (ops : Array Op) : Array Ops.Op :=
    ops.map Op.toSource

def toSourceOps (ops : Array Op) : Array Ops.Op :=
  ops.map Op.toSource

def hasStoreField (ops : Array Op) : Bool :=
  Ops.hasStoreField (toSourceOps ops)

def hasIndexSet (ops : Array Op) : Bool :=
  Ops.hasIndexSet (toSourceOps ops)

def hasCheckedArith (ops : Array Op) : Bool :=
  Ops.hasCheckedArith (toSourceOps ops)

def hasSelect (ops : Array Op) : Bool :=
  Ops.hasSelect (toSourceOps ops)

def hasInvoke (ops : Array Op) : Bool :=
  Ops.hasInvoke (toSourceOps ops)

structure Method where
  kind : Core.IR.MethodKind
  name : String
  ixName : String := ""
  paramCount : Nat := 0
  paramWidths : Array Nat := #[]
  retCount : Nat := 1
  ops : Array Op := #[]
  evaluation : Core.Evaluation Ops.ValKind := {}
  deriving BEq, Repr, Inhabited

/-- A statically addressed SVM account-data cell. Offsets include the eight-byte layout marker. -/
structure Slot where
  place : Option Core.Place := none
  name : String
  offset : Nat
  width : Nat
  abi : String
  deriving BEq, Repr, Inhabited

structure VectorLeaf where
  elementPath : Array Core.PathStep := #[]
  offset : Nat
  width : Nat
  deriving BEq, Repr, Inhabited

/-- Physical SVM layout for a fixed-length source vector. -/
structure Vector where
  place : Option Core.Place := none
  name : String
  baseOffset : Nat
  length : Nat
  strideBytes : Nat
  leaves : Array VectorLeaf := #[]
  deriving BEq, Repr, Inhabited

structure Program where
  name : String
  slots : Array Slot
  vectors : Array Vector := #[]
  schema : Core.Schema := {}
  methods : Array Method
  deriving BEq, Repr, Inhabited

private partial def rawSelfEntriesIn (ops : Array Op) :
    Except String (Array Ops.RawSelfEntry) := do
  let mut result := #[]
  for op in ops do
    match op with
    | .invoke _ metas data seeds bump =>
        let entries := data.filterMap Ops.CpiWord.rawSelfEntry?
        unless entries.isEmpty do
          match data[0]?, entries[0]?, metas.toList, seeds.toList, bump with
          | some (Ops.CpiWord.selfEntry tag authoritySeed), some entry,
              [authorityMeta], [.ascii signerSeed], some _ =>
              unless entries.size == 1 && entry.tag == tag &&
                  entry.authoritySeed == authoritySeed && signerSeed == authoritySeed &&
                  authorityMeta.signer && !authorityMeta.writable do
                throw "extract/unsupported: malformed raw self-entry invocation"
              result := result.push entry
          | _, _, _, _, _ =>
              throw "extract/unsupported: malformed raw self-entry invocation"
    | .ite _ _ _ thn els =>
        result := result ++ (← rawSelfEntriesIn thn) ++ (← rawSelfEntriesIn els)
    | .forBody _ body => result := result ++ (← rawSelfEntriesIn body)
    | _ => pure ()
  return result

/-- A program can expose at most one raw signed self-entry contract. -/
def rawSelfEntry? (program : Program) : Except String (Option Ops.RawSelfEntry) := do
  let mut found : Option Ops.RawSelfEntry := none
  for method in program.methods do
    for entry in ← rawSelfEntriesIn method.ops do
      match found with
      | none => found := some entry
      | some expected =>
          unless expected == entry do
            throw "extract/unsupported: inconsistent raw self-entry tags or authority seeds"
  return found

private def lowerSlots (src : Extract.IR.Program) : Array Slot := Id.run do
  let mut result := #[]
  let mut offset := 8
  for i in [0:src.slots.size] do
    let slot := src.slots[i]!
    result := result.push {
      place := (src.schema.leaves[i]?).map (·.place)
      name := slot.name
      offset
      width := slot.width
      abi := slot.abi
    }
    offset := offset + slot.width
  return result

private def lowerVectors (src : Extract.IR.Program) (slots : Array Slot) : Array Vector :=
  src.schema.vectors.filterMap fun vector => do
    let baseIndex ← src.schema.vectorBaseLeafIndex? vector
    let base ← slots[baseIndex]?
    let sourceLeaves := src.schema.vectorElementLeaves vector
    let leaves := sourceLeaves.mapIdx fun index leaf =>
      let offset := (sourceLeaves.extract 0 index).foldl (init := 0) fun n item =>
        n + item.width
      ({
        elementPath := leaf.place.steps.extract (vector.place.steps.size + 1)
        offset
        width := leaf.width
      } : VectorLeaf)
    return {
      place := some vector.place
      name := vector.name
      baseOffset := base.offset
      length := vector.length
      strideBytes := vector.elementBytes
      leaves
    }

private def lowerMethod (schema : Core.Schema) (method : Extract.IR.Method) :
    Except String Method := do
  let sourceOps ← Extract.IR.toSvmOps method.ops
  unless sourceOps.all Ops.Op.wellFormed do
    throw s!"extract/ir: malformed SVM Ops in {method.ixName}"
  let evaluation ←
    if schema.isEmpty then pure {}
    else Core.evaluate schema sourceOps
  return {
    kind := method.kind
    name := method.name
    ixName := method.ixName
    paramCount := method.paramCount
    paramWidths := method.paramWidths
    retCount := method.retCount
    ops := ← ofSourceOps sourceOps
    evaluation
  }

/-- Project the combined extractor dialect and lower it into an SVM-owned physical program. -/
def fromExtracted (src : Extract.IR.Program) : Except String Program := do
  src.validateSvm
  let slots := lowerSlots src
  let program : Program := {
    name := src.name
    slots
    vectors := lowerVectors src slots
    schema := src.schema
    methods := ← src.methods.mapM (lowerMethod src.schema)
  }
  let _ ← rawSelfEntry? program
  return program

def Program.fields (p : Program) : Array String :=
  p.slots.map (·.name)

def fieldOffset (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.offset)

def fieldWidth (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.width)

private def inferredVector? (p : Program) (name : String) : Option Vector :=
  let prefix0 := name ++ "_0"
  let group := p.slots.filter fun slot =>
    slot.name == prefix0 || slot.name.startsWith (prefix0 ++ "_")
  if group.isEmpty then none
  else
    let digitPrefix (value : String) : String := Id.run do
      let mut result := ""
      for char in value.toList do
        if char.isDigit then result := result.push char else return result
      return result
    let length := p.slots.foldl (init := 0) fun current slot =>
      let rest :=
        if slot.name.startsWith (name ++ "_") then
          digitPrefix (slot.name.drop (name.length + 1) |>.copy)
        else ""
      match rest.toNat? with
      | some index => Nat.max current (index + 1)
      | none => current
    let stride := group.foldl (init := 0) fun width slot => width + slot.width
    let base := p.slots.find? fun slot =>
      slot.name == prefix0 || slot.name.startsWith (prefix0 ++ "_")
    if length == 0 || stride == 0 then none
    else base.map fun slot =>
      { name, baseOffset := slot.offset, length, strideBytes := stride }

private def vector? (p : Program) (name : String) : Option Vector :=
  match p.vectors.find? (·.name == name) with
  | some vector => some vector
  | none => inferredVector? p name

def vectorBaseOffset (p : Program) (name : String) : Option Nat :=
  (vector? p name).map (·.baseOffset)

def vectorLenOf (p : Program) (name : String) (given : Nat) : Nat :=
  if given != 0 then given
  else (vector? p name).map (·.length) |>.getD 0

def vectorStride (p : Program) (name : String) : Nat :=
  (vector? p name).map (·.strideBytes) |>.getD 8

/-- Width of the leaf at one byte offset within a source vector element. -/
def vectorLeafWidth (p : Program) (name : String) (byteOffset : Nat) : Option Nat := do
  let vector ← vector? p name
  if vector.leaves.isEmpty then
    -- Legacy fixtures only model vectors of UInt64 leaves.
    some 8
  else
    (vector.leaves.find? (·.offset == byteOffset)).map (·.width)

def optionLeafNames? (p : Program) : Option (String × String) :=
  match p.schema.firstOption? with
  | some (tag, payload) => some (tag.name, payload.name)
  | none => do
      let tag ← p.slots.find? (fun slot => slot.name.endsWith "_tag")
      let payload ← p.slots.find? (fun slot => slot.name.endsWith "_p0")
      return (tag.name, payload.name)

def isProgramShape (p : Program) : Bool :=
  p.methods.any (·.kind == .init) &&
    p.methods.any (·.kind == .increment) &&
    p.methods.any (·.kind == .get)

def usesCpi (p : Program) : Bool :=
  p.methods.any (hasInvoke ·.ops)

def usesWalk (p : Program) : Bool :=
  usesCpi p || p.methods.any fun method => Ops.hasAcc1 (toSourceOps method.ops)

private partial def highestInvokeIndex (ops : Array Op) : Nat :=
  ops.foldl (init := 0) fun result op =>
    match op with
    | .invoke programIndex metas data .. =>
      let fromMetas := metas.foldl (init := Nat.max result programIndex) fun value entry =>
          Nat.max value entry.acc
      data.foldl (init := fromMetas) fun value word =>
        match word with
        | .accKey accountIndex => Nat.max value accountIndex
        | _ => value
    | .ite _ _ _ thn els =>
        Nat.max result (Nat.max (highestInvokeIndex thn) (highestInvokeIndex els))
    | .forBody _ body => Nat.max result (highestInvokeIndex body)
    | _ => result

def cpiAccountCount (p : Program) : Nat :=
  let highest := p.methods.foldl (init := 0) fun current method =>
    Nat.max current (highestInvokeIndex method.ops)
  -- CPI indices are relative to the external-account region; physical account 0 is state.
  let fromInvoke := if usesCpi p then Nat.max 3 (highest + 2) else 0
  let fromValues := p.methods.foldl (init := 0) fun current method =>
    Nat.max current (Ops.opsMinAccounts (toSourceOps method.ops))
  Nat.max fromInvoke fromValues

private def sourceSlots (p : Program) : Array Core.IR.Slot :=
  p.slots.map fun slot =>
    { name := slot.name, width := slot.width, abi := slot.abi }

def dataLen (p : Program) : Nat :=
  ABI.dataLenOf (sourceSlots p)

def inputLayout (p : Program) : ABI.InputLayout :=
  ABI.inputLayoutOf (dataLen p) (usesWalk p) (cpiAccountCount p)

def layoutMarkerHex (p : Program) : Except String String :=
  ABI.layoutMarkerHexOf (sourceSlots p)

private def kindTag : Core.IR.MethodKind → String
  | .init => "init"
  | .increment => "mut"
  | .get => "view"

private def cmpTag : Ops.Cmp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt"
  | .le => "le" | .gt => "gt" | .ge => "ge"

/-- Preserve the old closed-union spelling in canonical digests during the IR migration. -/
private def legacyCmpRepr (cmp : Ops.Cmp) : String :=
  "ProofForge.Ops.Cmp." ++ cmpTag cmp

private def pdaSeedCanon : Ops.PdaSeed → String
  | .ascii value => s!"s.{value}"
  | .stateKey => "state"
  | .accKey i => s!"k.{i}"

private partial def valCanon : Ops.Val → String
  | .arg i => s!"a{i}"
  | .local i => s!"v{i}"
  | .lit n => s!"l{n.toNat}"
  | .field base name => s!"f.{name}({valCanon base})"
  | .ext .clockSlot #[] => "clk"
  | .ext .clockEpoch #[] => "epo"
  | .ext .unixTime #[] => "unix"
  | .ext .slotsPerEpoch #[] => "spe"
  | .ext .signerKey0 #[] => "k0"
  | .ext .accLamports0 #[] => "lp0"
  | .ext .accOwner0 #[] => "ow0"
  | .ext .accDataLen0 #[] => "dl0"
  | .ext .accN #[] => "nacc"
  | .ext .isSigner0 #[] => "sg0"
  | .ext .isWritable0 #[] => "wr0"
  | .ext .isExecutable0 #[] => "ex0"
  | .ext .accLamports1 #[] => "lp1"
  | .ext .accOwner1 #[] => "ow1"
  | .ext .accDataLen1 #[] => "dl1"
  | .ext .isSigner1 #[] => "sg1"
  | .ext .isWritable1 #[] => "wr1"
  | .ext .isExecutable1 #[] => "ex1"
  | .ext (.findPda seed) #[] => s!"pda.{seed}"
  | .ext (.checkPda seed) #[bump] => s!"chk.{seed}:{valCanon bump}"
  | .ext (.rentExemption len) #[] => s!"rent.{len.toNat}"
  | .ext .cpiReturn #[] => "cret"
  | .ext (.sha256Lit seed) #[] => s!"sha.{seed}"
  | .ext (.keccak256Lit seed) #[] => s!"kec.{seed}"
  | .ext (.accKeyWord acc word) #[] => s!"kw.{acc}.{word}"
  | .ext (.accOwnerWord acc word) #[] => s!"ow.{acc}.{word}"
  | .ext (.accLamportsN acc) #[] => s!"lpN.{acc}"
  | .ext (.accDataLenN acc) #[] => s!"dlN.{acc}"
  | .ext (.isSignerN acc) #[] => s!"sgN.{acc}"
  | .ext (.isWritableN acc) #[] => s!"wrN.{acc}"
  | .ext (.isExecutableN acc) #[] => s!"exN.{acc}"
  | .ext (.signerKeyN acc) #[] => s!"sk.{acc}"
  | .ext (.ownerIsSelf acc) #[] => s!"ois.{acc}"
  | .ext (.findPdaSeeds seeds) #[] =>
      s!"pdas.[{String.intercalate "," (seeds.toList.map pdaSeedCanon)}]"
  | .ext (.checkPdaSeeds account seeds) #[] =>
      s!"chkpdas.{account}.[{String.intercalate "," (seeds.toList.map pdaSeedCanon)}]"
  | .bitAnd lhs rhs => s!"and({valCanon lhs},{valCanon rhs})"
  | .bitOr lhs rhs => s!"or({valCanon lhs},{valCanon rhs})"
  | .bitXor lhs rhs => s!"xor({valCanon lhs},{valCanon rhs})"
  | .bitNot value => s!"not({valCanon value})"
  | .shiftL lhs rhs => s!"shl({valCanon lhs},{valCanon rhs})"
  | .shiftR lhs rhs => s!"shr({valCanon lhs},{valCanon rhs})"
  | .indexGet base name index len offset =>
      if offset == 0 then s!"idx.{name}[{valCanon index}/{len}]({valCanon base})"
      else s!"idx.{name}+{offset}[{valCanon index}/{len}]({valCanon base})"
  | .loopIx => "ix"
  | .select cmp lhs rhs thn els =>
      s!"sel.{legacyCmpRepr cmp}({valCanon lhs},{valCanon rhs},{valCanon thn},{valCanon els})"
  | .addU64 lhs rhs => s!"uadd({valCanon lhs},{valCanon rhs})"
  | .subU64 lhs rhs => s!"usub({valCanon lhs},{valCanon rhs})"
  | .mulU64 lhs rhs => s!"umul({valCanon lhs},{valCanon rhs})"
  | .divU64 lhs rhs => s!"udiv({valCanon lhs},{valCanon rhs})"
  | .modU64 lhs rhs => s!"umod({valCanon lhs},{valCanon rhs})"
  | .ext kind operands =>
      s!"ext.{repr kind}({String.intercalate "," (operands.map valCanon).toList})"

private partial def opsCanon (ops : Array Op) : String :=
  let one (op : Op) : String :=
    match op with
    | .letLocal i value => s!"let.{i}({valCanon value})"
    | .joinLocal i => s!"join.{i}"
    | .setLocal i value => s!"set.{i}({valCanon value})"
    | .checkedAddU64 lhs rhs => s!"add({valCanon lhs},{valCanon rhs})"
    | .checkedSubU64 lhs rhs => s!"sub({valCanon lhs},{valCanon rhs})"
    | .checkedMulU64 lhs rhs => s!"mul({valCanon lhs},{valCanon rhs})"
    | .checkedDivU64 lhs rhs => s!"div({valCanon lhs},{valCanon rhs})"
    | .checkedModU64 lhs rhs => s!"mod({valCanon lhs},{valCanon rhs})"
    | .ite cmp lhs rhs thn els =>
        s!"ite.{cmpTag cmp}({valCanon lhs},{valCanon rhs},[{opsCanon thn}],[{opsCanon els}])"
    | .invoke programIx metas data seeds bump =>
        let metaCanon := String.intercalate "," <| metas.toList.map fun entry =>
          s!"{entry.acc}{if entry.signer then "s" else ""}{if entry.writable then "w" else ""}"
        let wordCanon (word : Ops.CpiWord Ops.Val) : String :=
          match word with
          | .u8le (.lit n) => s!"u8.{n.toNat}"
          | .u8le value => s!"u8v.{valCanon value}"
          | .u16le value => s!"u16.{valCanon value}"
          | .u32le (.lit n) => s!"u32.{n.toNat}"
          | .u32le value => s!"u32v.{valCanon value}"
          | .u64le value => s!"u64.{valCanon value}"
          | .selfEntry tag authoritySeed => s!"self.{tag.toNat}.{authoritySeed}"
          | .ascii value => s!"s.{value}"
          | .programId => "pid"
          | .accKey i => s!"k.{i}"
        let dataCanon := String.intercalate "," (data.toList.map wordCanon)
        let signer :=
          match seeds.toList, bump with
          -- Preserve the v1 spelling, and therefore existing fixture digests, for the original
          -- one-ASCII-seed signer shape.
          | [.ascii value], some valueBump => s!",s.{value}:{valCanon valueBump}"
          | _, some valueBump =>
              let seedCanon := String.intercalate "," (seeds.toList.map pdaSeedCanon)
              s!",s.[{seedCanon}]:{valCanon valueBump}"
          | _, none => ""
        s!"inv({programIx},[{metaCanon}],[{dataCanon}]{signer})"
    | .forAccum n addend resultLocal =>
        s!"for.{resultLocal}({n},{valCanon addend})"
    | .forBody n body => s!"forb({n},[{opsCanon body}])"
    | .indexSet name index value len offset =>
        if offset == 0 then s!"iset.{name}[{valCanon index}/{len}]({valCanon value})"
        else s!"iset.{name}+{offset}[{valCanon index}/{len}]({valCanon value})"
    | .storeField name value => s!"st.{name}({valCanon value})"
    | .okState value => s!"ok({valCanon value})"
    | .errorOverflow => "ovf"
    | .errorNamed name => s!"err.{name}"
    | .returnU64 value => s!"retu({valCanon value})"
    | .returnState value => s!"rets({valCanon value})"
  String.intercalate ";" (ops.toList.map one)

/-- Stable source identity, computed from SVM-owned Ops without rebuilding the mixed legacy IR. -/
def canonical (p : Program) : String :=
  let fields := String.intercalate "," p.fields.toList
  let methods :=
    (p.methods.qsort (fun lhs rhs => lhs.ixName < rhs.ixName)).toList.map fun method =>
      let base :=
        s!"{kindTag method.kind}:{method.ixName}:{method.paramCount}:[{opsCanon method.ops}]"
      if (method.paramWidths.isEmpty || method.paramWidths.all (· == 8)) && method.retCount == 1 then
        base
      else
        let widths := String.intercalate "," (method.paramWidths.map toString).toList
        s!"{kindTag method.kind}:{method.ixName}:{method.paramCount}:{widths}:r{method.retCount}:[{opsCanon method.ops}]"
  s!"{p.name}|{fields}|{String.intercalate "/" methods}"

def digestHex (p : Program) : String :=
  Core.IR.u64Hex (Core.IR.fnv1a64 (canonical p))

def discHex (m : Method) : Except String String :=
  ABI.discHexOf m.ixName m.paramCount

def lastName := Core.IR.lastName
def ixNameOfLean := Core.IR.ixNameOfLean
def u64Hex := Core.IR.u64Hex

end ProofForge.Svm.IR
