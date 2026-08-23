import ProofForge.IR
import ProofForge.Ops
import ProofForge.Crypto.Keccak

namespace ProofForge.Evm.IR

open ProofForge.Crypto

structure Slot where
  name : String
  index : Nat
  /-- 物理宽：1/2/4/8。EVM 仍占一个 storage word，窄值在低字节。 -/
  width : Nat := 8
  deriving BEq, Repr, Inhabited

structure Method where
  kind : ProofForge.IR.MethodKind
  name : String
  ixName : String
  selector : String := ""
  paramCount : Nat := 0
  paramWidths : Array Nat := #[]
  retCount : Nat := 1
  ops : Array Ops.Op := #[]
  view : Bool := false
  payable : Bool := false
  deriving BEq, Repr, Inhabited

structure Program where
  name : String
  slots : Array Slot
  constructor : Method
  entries : Array Method
  deriving BEq, Repr, Inhabited

def slotIndex (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.index)

def slotWidth (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.width)

def hasOptionLeaves (p : Program) : Bool :=
  p.slots.any (fun s => s.name.endsWith "_tag")

private def valForbidden : Ops.Val → Bool
  | .clockSlot | .clockEpoch | .slotsPerEpoch | .signerKey0
  | .accLamports0 | .accOwner0 | .accDataLen0 | .accN
  | .isSigner0 | .isWritable0 | .isExecutable0
  | .accLamports1 | .accOwner1 | .accDataLen1
  | .isSigner1 | .isWritable1 | .isExecutable1
  | .findPda _ | .checkPda .. | .rentExemption _ | .cpiReturn
  | .sha256Lit _ | .keccak256Lit _ | .accKeyWord .. | .accOwnerWord .. => true
  | .unixTime | .accLamportsN _ | .accDataLenN _ | .isSignerN _
  | .isWritableN _ | .isExecutableN _ | .signerKeyN _ | .ownerIsSelf _ => true
  | .field b _ => valForbidden b
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r =>
      valForbidden l || valForbidden r
  | .bitNot v => valForbidden v
  | .indexGet b _ i _ => valForbidden b || valForbidden i
  | _ => false

private def walkForbidden (fuel : Nat) (ops : Array Ops.Op) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    ops.any fun
      | .invoke .. => true
      | .checkedAddU64 l r => valForbidden l || valForbidden r
      | .checkedSubU64 l r => valForbidden l || valForbidden r
      | .checkedMulU64 l r => valForbidden l || valForbidden r
      | .checkedDivU64 l r => valForbidden l || valForbidden r
      | .checkedModU64 l r => valForbidden l || valForbidden r
      | .ite _ l r t f =>
          valForbidden l || valForbidden r ||
            walkForbidden fuel' t || walkForbidden fuel' f
      | .storeField _ v => valForbidden v
      | .okState v => valForbidden v
      | .returnU64 v => valForbidden v
      | .returnState v => valForbidden v
      | .evmDeposit v => valForbidden v
      | .evmSendEth a b c d =>
          valForbidden a || valForbidden b || valForbidden c || valForbidden d
      | .evmLog _ v => valForbidden v
      | .forAccum _ v => valForbidden v
      | .forBody _ body => walkForbidden fuel' body
      | .indexSet _ i v _ => valForbidden i || valForbidden v
      | .mapGetU64 a b => valForbidden a || valForbidden b
      | .mapSetU64 a b c => valForbidden a || valForbidden b || valForbidden c
      | .mapGetAddr a b c d =>
          valForbidden a || valForbidden b || valForbidden c || valForbidden d
      | .mapSetAddr a b c d e =>
          valForbidden a || valForbidden b || valForbidden c ||
            valForbidden d || valForbidden e
      | .mapGetPair a b c d e f g =>
          valForbidden a || valForbidden b || valForbidden c || valForbidden d ||
            valForbidden e || valForbidden f || valForbidden g
      | .mapSetPair a b c d e f g h =>
          valForbidden a || valForbidden b || valForbidden c || valForbidden d ||
            valForbidden e || valForbidden f || valForbidden g || valForbidden h
      | .evmTokenTransfer a b c d e f g =>
          valForbidden a || valForbidden b || valForbidden c || valForbidden d ||
            valForbidden e || valForbidden f || valForbidden g
      | .evmTokenBalanceOfSelf a b c =>
          valForbidden a || valForbidden b || valForbidden c
      | .errorOverflow | .errorNamed _ => false

def hasSvmLeaf (ops : Array Ops.Op) : Bool :=
  walkForbidden 16 ops

private def rejectSlot (s : ProofForge.IR.Slot) : Option String :=
  if !(s.width == 1 || s.width == 2 || s.width == 4 || s.width == 8) then
    some s!"extract/unsupported: evm slot {s.name} width {s.width}"
  else none

private def isCtor (m : ProofForge.IR.Method) : Bool :=
  m.kind == .init

/-- 从已抽出的 SVM `IR.Program` 做成 EVM 形状。不改原 IR。 -/
def fromProgram (src : ProofForge.IR.Program) : Except String Program := do
  if src.slots.isEmpty then
    throw "extract/unsupported: evm program has no slots"
  for s in src.slots do
    if let some reason := rejectSlot s then
      throw reason
  let mut ctors : Array ProofForge.IR.Method := #[]
  let mut extras : Array ProofForge.IR.Method := #[]
  for m in src.methods do
    if hasSvmLeaf m.ops then
      throw s!"extract/unsupported: evm rejects svm leaf in {m.ixName}"
    if isCtor m then
      ctors := ctors.push m
    else
      extras := extras.push m
  if ctors.isEmpty then
    throw "extract/unsupported: evm wants a constructor"
  let ctorSrc :=
    match ctors.find? (fun m =>
        m.ixName == "initialize" || ProofForge.IR.lastName m.name == "init") with
    | some m => m
    | none => ctors[0]!
  let rest :=
    extras ++ ctors.filter (fun m => m.ixName != ctorSrc.ixName || m.name != ctorSrc.name)
  if rest.isEmpty then
    throw "extract/unsupported: evm wants at least one entry"
  if ctorSrc.ops.isEmpty then
    throw "extract/unsupported: init missing returnState"
  unless ctorSrc.ops.any (fun | .returnState _ => true | _ => false) do
    throw "extract/unsupported: init missing returnState"
  let ctor : Method := {
    kind := ctorSrc.kind
    name := ctorSrc.name
    ixName := ctorSrc.ixName
    selector := ""
    paramCount := ctorSrc.paramCount
    paramWidths := ctorSrc.paramWidths
    retCount := 1
    ops := ctorSrc.ops
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
    entries := entries.push {
      kind := m.kind
      name := m.name
      ixName := m.ixName
      selector := sel
      paramCount := m.paramCount
      paramWidths := widths
      retCount := m.retCount
      ops := m.ops
      view
      payable := !view && Ops.hasEvmDeposit m.ops
    }
  let slots := src.slots.mapIdx fun i s =>
    { name := s.name, index := i, width := s.width }
  return { name := src.name, slots, constructor := ctor, entries }

private def cmpTag : Ops.Cmp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt"
  | .le => "le" | .gt => "gt" | .ge => "ge"

private def valCanon : Ops.Val → String
  | .arg i => s!"a{i}"
  | .lit n => s!"l{n.toNat}"
  | .field b n => s!"f.{n}({valCanon b})"
  | .clockSlot => "clk"
  | .clockEpoch => "epo"
  | .slotsPerEpoch => "spe"
  | .signerKey0 => "k0"
  | .accLamports0 => "lp0"
  | .accOwner0 => "ow0"
  | .accDataLen0 => "dl0"
  | .accN => "nacc"
  | .isSigner0 => "sg0"
  | .isWritable0 => "wr0"
  | .isExecutable0 => "ex0"
  | .accLamports1 => "lp1"
  | .accOwner1 => "ow1"
  | .accDataLen1 => "dl1"
  | .isSigner1 => "sg1"
  | .isWritable1 => "wr1"
  | .isExecutable1 => "ex1"
  | .findPda s => s!"pda.{s}"
  | .checkPda s b => s!"chk.{s}:{valCanon b}"
  | .rentExemption n => s!"rent.{n.toNat}"
  | .cpiReturn => "cret"
  | .sha256Lit s => s!"sha.{s}"
  | .keccak256Lit s => s!"kec.{s}"
  | .accKeyWord a w => s!"kw.{a}.{w}"
  | .accOwnerWord a w => s!"ow.{a}.{w}"
  | .evmCaller => "ecall"
  | .evmBlockNumber => "eblk"
  | .evmTimestamp => "ets"
  | .evmChainId => "echain"
  | .evmSelf => "eself"
  | .evmCallValue => "eval"
  | .evmSelfBalance => "ebal"
  | .evmCallerW0 => "ecw0"
  | .evmCallerW1 => "ecw1"
  | .evmCallerW2 => "ecw2"
  | .evmSelfW0 => "esw0"
  | .evmSelfW1 => "esw1"
  | .evmSelfW2 => "esw2"
  | .bitAnd l r => s!"and({valCanon l},{valCanon r})"
  | .bitOr l r => s!"or({valCanon l},{valCanon r})"
  | .bitXor l r => s!"xor({valCanon l},{valCanon r})"
  | .bitNot v => s!"not({valCanon v})"
  | .shiftL l r => s!"shl({valCanon l},{valCanon r})"
  | .shiftR l r => s!"shr({valCanon l},{valCanon r})"
  | .indexGet b n i k => s!"idx.{n}[{valCanon i}/{k}]({valCanon b})"
  | .loopIx => "ix"
  | .unixTime => "unix"
  | .accLamportsN a => s!"lpN.{a}"
  | .accDataLenN a => s!"dlN.{a}"
  | .isSignerN a => s!"sgN.{a}"
  | .isWritableN a => s!"wrN.{a}"
  | .isExecutableN a => s!"exN.{a}"
  | .signerKeyN a => s!"sk.{a}"
  | .ownerIsSelf a => s!"ois.{a}"
  | .addU64 l r => s!"uadd({valCanon l},{valCanon r})"
  | .subU64 l r => s!"usub({valCanon l},{valCanon r})"
  | .mapGetU64 b k => s!"vg({valCanon b},{valCanon k})"
  | .mapGetAddr b a0 a1 a2 =>
      s!"vga({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2})"
  | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
      s!"vgp({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2},{valCanon c0},{valCanon c1},{valCanon c2})"

private partial def opsCanon (ops : Array Ops.Op) : String :=
  let rec one (op : Ops.Op) : String :=
    match op with
    | .checkedAddU64 l r => s!"add({valCanon l},{valCanon r})"
    | .checkedSubU64 l r => s!"sub({valCanon l},{valCanon r})"
    | .checkedMulU64 l r => s!"mul({valCanon l},{valCanon r})"
    | .checkedDivU64 l r => s!"div({valCanon l},{valCanon r})"
    | .checkedModU64 l r => s!"mod({valCanon l},{valCanon r})"
    | .ite c l r t f => s!"ite.{cmpTag c}({valCanon l},{valCanon r},[{opsCanon t}],[{opsCanon f}])"
    | .invoke .. => "inv"
    | .evmDeposit v => s!"edep({valCanon v})"
    | .evmSendEth a b c d =>
        s!"esend({valCanon a},{valCanon b},{valCanon c},{valCanon d})"
    | .evmLog n v => s!"elog.{n}({valCanon v})"
    | .forAccum n v => s!"for({n},{valCanon v})"
    | .forBody n body => s!"forb({n},[{opsCanon body}])"
    | .indexSet n i v k => s!"iset.{n}[{valCanon i}/{k}]({valCanon v})"
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
  ProofForge.IR.u64Hex (ProofForge.IR.fnv1a64 (canonical p))

end ProofForge.Evm.IR
