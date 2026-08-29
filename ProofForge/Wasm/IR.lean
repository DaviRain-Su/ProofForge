import ProofForge.Extract.IR
import ProofForge.Core.Target
import ProofForge.Wasm.Family

/-!
# WASM 家族 IR 核心（链共享）

WASM 家族共享的程序形状、v0 子集检查与 canonical digest 拼写，对链方言类型
（`ValExt` / `OpExt`）泛型。链间差异——host import 表、存储布局、入口 ABI——
由 `ProofForge.Wasm.Host.Contract` 注入发射器，不进这一层；每条链自己的
registration 实例化见 `Wasm/<Chain>/IR.lean`。产物是 `.wasm`（wsm-002）；
wsm-001 仍经同一 IR 发 Rust 源，那是过渡。

v0 子集（对家族所有链 fail closed；链方言可以更严，不能更松）：

- state：`UInt64` 叶（slot width 8）；
- params：scalar `UInt64`；view 结果恰好一个 `UInt64`；mutating entry 只返回
  状态码（源声明的 public 返回值省略，`echoDropped` 记录）；
- ops：checked 五则、`ite`、`okState` / `returnState` / `returnU64`、
  `errorOverflow`、钉死的 `errorNamed "unauthorized"`（状态码 3）和
  `errorNamed "paused"`（状态码 4）、`storeField`。
  loop / local / 运行时 vector 下标 / map / 其它 named error / 位运算 / 未检查 `/ %`
  全部拒绝。编译期 `Vector UInt64 n` 叶、字面量下标、`forAccum`（上界 1..8）
  先展开成命名槽 / nested `addU64`，再过这道门。
- 无宿主 capability 叶：ledger time / caller / hashing 由各链在自己的方言里钉。
-/

namespace ProofForge.Wasm.IR

abbrev Op (ValExt : Type) (OpExt : Type → Type) := ProofForge.Core.Ops.Op ValExt OpExt
abbrev Val (ValExt : Type) := ProofForge.Core.Ops.Val ValExt
abbrev Cmp := ProofForge.Core.Ops.Cmp

/-- Build one chain's registration from its dialect plumbing; foreign svm/evm leaves
are rejected through the family-level convention with the chain name as prefix. -/
def mkRegistration {ValExt : Type} {OpExt : Type → Type}
    (chain : String) (valArity : ValExt → Nat)
    (cfgDialect : Core.CFG.Dialect ValExt OpExt)
    (opWellFormed : Op ValExt OpExt → Bool)
    (projectValExt : Extract.IR.ValKind → Except String ValExt := Family.rejectValKind chain)
    (projectOpExt : (Extract.IR.Val → Except String (Val ValExt)) →
      Extract.IR.OpExt Extract.IR.Val → Except String (OpExt (Val ValExt)) :=
        fun _ payload => Family.rejectOpExt chain payload) :
    Core.Target.Registration Extract.IR.ValKind Extract.IR.OpExt ValExt OpExt where
  name := chain.toUpper
  projectValExt := projectValExt
  projectOpExt := projectOpExt
  projectionError := fun method reason =>
    if reason.startsWith s!"extract/unsupported: {chain} rejects" then
      s!"{reason} in {method}"
    else reason
  valArity := valArity
  opWellFormed := opWellFormed
  cfgDialect := cfgDialect

/-- One lowered method. `tupleArity = some _` marks an infallible single-value view;
`none` selects the status ABI (initializer and mutating entries). `echoDropped`
records that the source also declared a public result value which the status ABI does
not carry on-chain. -/
structure Method (ValExt : Type) (OpExt : Type → Type) where
  kind : Core.IR.MethodKind
  name : String
  ixName : String
  paramCount : Nat := 0
  /-- Optional target-owned logical input shape retained after parameters are rewritten to a
  fixed scalar frame. Empty for the historical raw-u64 ABI and for XRPL. -/
  inputSchema : Option Core.Codec.Schema := none
  /-- Canonical target-owned input policy. This participates in the digest only when nonempty. -/
  inputPolicy : String := ""
  /-- Optional target-owned logical output retained after a bounded result is rewritten to the
  physical scalar metadata accepted by the shared WASM gate. -/
  outputSchema : Option Core.Codec.Schema := none
  /-- Canonical target-owned output policy. Empty preserves historical target digests. -/
  outputPolicy : String := ""
  tupleArity : Option Nat := none
  echoDropped : Bool := false
  ops : Array (Op ValExt OpExt) := #[]
  evaluation : Core.Evaluation ValExt := {}
  deriving Inhabited

structure Program (ValExt : Type) (OpExt : Type → Type) where
  name : String
  slots : Array Core.IR.Slot
  initializer : Method ValExt OpExt
  entries : Array (Method ValExt OpExt)
  deriving Inhabited

def slotNames (p : Program ValExt OpExt) : Array String :=
  p.slots.map (·.name)

/-! ## Compile-time vector / forAccum lowering

WASM v0 does not emit `loop` / `loopIx` / runtime `indexGet`. A `Vector UInt64 n`
already flattens to slots `name_0`…`name_{n-1}`. Literal indices and bounded
`forAccum` become those named slots and nested `addU64`. Runtime index and
`forBody` stay rejected. -/

private partial def substLoopIx {ValExt : Type} (i : UInt64) : Val ValExt → Val ValExt
  | .loopIx => .lit i
  | .field base n => .field (substLoopIx i base) n
  | .indexGet base n idx len off =>
      .indexGet (substLoopIx i base) n (substLoopIx i idx) len off
  | .select cmp lhs rhs thn els =>
      .select cmp (substLoopIx i lhs) (substLoopIx i rhs)
        (substLoopIx i thn) (substLoopIx i els)
  | .addU64 lhs rhs => .addU64 (substLoopIx i lhs) (substLoopIx i rhs)
  | .subU64 lhs rhs => .subU64 (substLoopIx i lhs) (substLoopIx i rhs)
  | .mulU64 lhs rhs => .mulU64 (substLoopIx i lhs) (substLoopIx i rhs)
  | .divU64 lhs rhs => .divU64 (substLoopIx i lhs) (substLoopIx i rhs)
  | .modU64 lhs rhs => .modU64 (substLoopIx i lhs) (substLoopIx i rhs)
  | .bitAnd lhs rhs => .bitAnd (substLoopIx i lhs) (substLoopIx i rhs)
  | .bitOr lhs rhs => .bitOr (substLoopIx i lhs) (substLoopIx i rhs)
  | .bitXor lhs rhs => .bitXor (substLoopIx i lhs) (substLoopIx i rhs)
  | .bitNot v => .bitNot (substLoopIx i v)
  | .shiftL lhs rhs => .shiftL (substLoopIx i lhs) (substLoopIx i rhs)
  | .shiftR lhs rhs => .shiftR (substLoopIx i lhs) (substLoopIx i rhs)
  | .ext kind operands => .ext kind (operands.map (substLoopIx i))
  | v => v

private partial def lowerVal {ValExt : Type} : Val ValExt → Except String (Val ValExt)
  | .arg i => .ok (.arg i)
  | .lit n => .ok (.lit n)
  | .loopIx => .error "extract/unsupported: wasm v0 rejects loopIx"
  | .local _ => .error "extract/unsupported: wasm v0 rejects local"
  | .field base n =>
      match lowerVal base with
      | .error e => .error e
      | .ok b => .ok (.field b n)
  | .indexGet base n (.lit k) len 0 =>
      -- Extracted `len` is often 0; the real bound lives on Schema / slot names.
      if len != 0 && k.toNat ≥ len then
        .error s!"extract/unsupported: wasm v0 vector index {k.toNat} ≥ {len}"
      else
        lowerVal (.field base s!"{n}_{k.toNat}")
  | .indexGet _ _ _ _ off =>
      if off != 0 then
        .error "extract/unsupported: wasm v0 rejects vector element offset"
      else
        .error "extract/unsupported: wasm v0 rejects runtime vector index"
  | .select cmp lhs rhs thn els =>
      match lowerVal lhs, lowerVal rhs, lowerVal thn, lowerVal els with
      | .ok l, .ok r, .ok t, .ok f => .ok (.select cmp l r t f)
      | .error e, _, _, _ => .error e
      | _, .error e, _, _ => .error e
      | _, _, .error e, _ => .error e
      | _, _, _, .error e => .error e
  | .addU64 lhs rhs =>
      match lowerVal lhs, lowerVal rhs with
      | .ok l, .ok r => .ok (.addU64 l r)
      | .error e, _ => .error e
      | _, .error e => .error e
  | .subU64 lhs rhs =>
      match lowerVal lhs, lowerVal rhs with
      | .ok l, .ok r => .ok (.subU64 l r)
      | .error e, _ => .error e
      | _, .error e => .error e
  | .mulU64 lhs rhs =>
      match lowerVal lhs, lowerVal rhs with
      | .ok l, .ok r => .ok (.mulU64 l r)
      | .error e, _ => .error e
      | _, .error e => .error e
  | .ext kind operands =>
      if operands.isEmpty then .ok (.ext kind operands)
      else if operands.size == 3 then
        match lowerVal operands[0]!, lowerVal operands[1]!, lowerVal operands[2]! with
        | .ok a, .ok b, .ok c => .ok (.ext kind #[a, b, c])
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
      else .error "extract/unsupported: wasm v0 rejects ext operands"
  | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot _ | .shiftL .. | .shiftR ..
  | .divU64 .. | .modU64 .. =>
      .error "extract/unsupported: wasm v0 value"

private partial def lowerOpsList {ValExt : Type} {OpExt : Type → Type} :
    List (Op ValExt OpExt) → Except String (Array (Op ValExt OpExt))
  | [] => pure #[]
  | .forAccum n addend resultLocal :: rest => do
      unless n > 0 && n ≤ 8 do
        throw "extract/unsupported: wasm v0 forAccum bound must be 1..8"
      let rec nest (i : Nat) (acc : Val ValExt) : Val ValExt :=
        if i == n then acc
        else nest (i + 1) (.addU64 acc (substLoopIx (UInt64.ofNat i) addend))
      let sum ← lowerVal (nest 0 (.lit 0))
      match rest with
      | .returnU64 (.local j) :: more =>
          unless j == resultLocal do
            throw "extract/unsupported: wasm v0 forAccum result local mismatch"
          return #[.returnU64 sum] ++ (← lowerOpsList more)
      | _ =>
          throw "extract/unsupported: wasm v0 forAccum wants returnU64 of the accumulator"
  | .indexSet name (.lit k) value len 0 :: rest => do
      unless len == 0 || k.toNat < len do
        throw s!"extract/unsupported: wasm v0 vector index {k.toNat} ≥ {len}"
      let v ← lowerVal value
      return #[.storeField s!"{name}_{k.toNat}" v] ++ (← lowerOpsList rest)
  | .indexSetLeaf name (.lit k) value len leaf :: rest => do
      unless len == 0 || k.toNat < len do
        throw s!"extract/unsupported: wasm v0 vector index {k.toNat} ≥ {len}"
      unless leaf.isEmpty do
        throw "extract/unsupported: wasm v0 rejects named vector element leaves"
      let v ← lowerVal value
      return #[.storeField s!"{name}_{k.toNat}" v] ++ (← lowerOpsList rest)
  | .indexSet .. :: _ | .indexSetLeaf .. :: _ =>
      throw "extract/unsupported: wasm v0 rejects runtime vector index"
  | .forBody .. :: _ =>
      throw "extract/unsupported: wasm v0 rejects forBody (no wasm loop)"
  | .ite cmp lhs rhs thn els :: rest => do
      let l ← lowerVal lhs
      let r ← lowerVal rhs
      let thn' ← lowerOpsList thn.toList
      let els' ← lowerOpsList els.toList
      return #[.ite cmp l r thn' els'] ++ (← lowerOpsList rest)
  | .storeField n v :: rest => do
      let v ← lowerVal v
      return #[.storeField n v] ++ (← lowerOpsList rest)
  | .okState v :: rest => do
      let v ← lowerVal v
      return #[.okState v] ++ (← lowerOpsList rest)
  | .returnState v :: rest => do
      let v ← lowerVal v
      return #[.returnState v] ++ (← lowerOpsList rest)
  | .returnU64 v :: rest => do
      let v ← lowerVal v
      return #[.returnU64 v] ++ (← lowerOpsList rest)
  | .checkedAddU64 l r :: rest => do
      let l ← lowerVal l
      let r ← lowerVal r
      return #[.checkedAddU64 l r] ++ (← lowerOpsList rest)
  | .checkedSubU64 l r :: rest => do
      let l ← lowerVal l
      let r ← lowerVal r
      return #[.checkedSubU64 l r] ++ (← lowerOpsList rest)
  | .checkedMulU64 l r :: rest => do
      let l ← lowerVal l
      let r ← lowerVal r
      return #[.checkedMulU64 l r] ++ (← lowerOpsList rest)
  | .checkedDivU64 l r :: rest => do
      let l ← lowerVal l
      let r ← lowerVal r
      return #[.checkedDivU64 l r] ++ (← lowerOpsList rest)
  | .checkedModU64 l r :: rest => do
      let l ← lowerVal l
      let r ← lowerVal r
      return #[.checkedModU64 l r] ++ (← lowerOpsList rest)
  | .errorOverflow :: rest =>
      return #[.errorOverflow] ++ (← lowerOpsList rest)
  | .errorNamed n :: rest =>
      return #[.errorNamed n] ++ (← lowerOpsList rest)
  | .ext payload :: rest =>
      return #[.ext payload] ++ (← lowerOpsList rest)
  | _ :: _ =>
      throw "extract/unsupported: wasm v0 op"

private def lowerOps {ValExt : Type} {OpExt : Type → Type}
    (ops : Array (Op ValExt OpExt)) : Except String (Array (Op ValExt OpExt)) :=
  lowerOpsList ops.toList

/-! ## v0 subset checks -/

/-- Values the v0 WAT renderer can express. Guard computations use wrapping
two's-complement `i64.add/sub/mul`; unchecked `/ %` is rejected because divide-by-zero
traps outside the checked path. -/
partial def valAllowed {ValExt : Type} : Val ValExt → Bool
  | .arg _ | .lit _ => true
  | .field (.arg _) _ => true
  | .select _ lhs rhs thn els =>
      valAllowed lhs && valAllowed rhs && valAllowed thn && valAllowed els
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs =>
      valAllowed lhs && valAllowed rhs
  -- Target registration checks extension arity; the chain emitter owns the intrinsic and may
  -- consume recursively valid scalar operands (for example a bounded NEAR memory index).
  | .ext _ operands => operands.all valAllowed
  | _ => false

/-- Ops the v0 WAT renderer can express. -/
partial def opAllowed {ValExt : Type} {OpExt : Type → Type} : Op ValExt OpExt → Bool
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
      valAllowed lhs && valAllowed rhs
  | .ite _ lhs rhs thn els =>
      valAllowed lhs && valAllowed rhs && thn.all opAllowed && els.all opAllowed
  | .storeField _ value | .okState value | .returnState value | .returnU64 value =>
      valAllowed value
  -- Target registration already checked the payload; the chain emitter owns rendering.
  | .ext _ => true
  | .errorOverflow => true
  | .errorNamed "unauthorized" => true
  | .errorNamed "paused" => true
  | _ => false

/-- Views are infallible on-chain reads: any checked or error op is rejected. -/
partial def hasFallible {ValExt : Type} {OpExt : Type → Type} (ops : Array (Op ValExt OpExt)) : Bool :=
  ops.any fun
    | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
    | .checkedDivU64 .. | .checkedModU64 .. | .errorOverflow | .errorNamed _ => true
    | .ite _ _ _ thn els => hasFallible thn || hasFallible els
    | _ => false

private def isScalarU64 : Core.Codec.Schema → Bool
  | .scalar (.uint 64) => true
  | _ => false

private def checkParams {ValExt : Type} {OpExt : Type → Type}
    (method : Core.IR.Method ValExt OpExt) : Except String Unit := do
  unless method.paramSchemas.all isScalarU64 do
    throw s!"extract/unsupported: {method.ixName} wants UInt64 scalar parameters for wasm v0"
  unless method.paramWidths.isEmpty || method.paramWidths.all (· == 8) do
    throw s!"extract/unsupported: {method.ixName} wants UInt64 scalar parameters for wasm v0"
  unless method.paramTypes.isEmpty || method.paramTypes.all (· == .uint 64) do
    throw s!"extract/unsupported: {method.ixName} wants UInt64 scalar parameters for wasm v0"

private def checkViewReturn {ValExt : Type} {OpExt : Type → Type}
    (method : Core.IR.Method ValExt OpExt) : Except String Unit := do
  unless method.retTypes.isEmpty || method.retTypes.all (· == .uint 64) do
    throw s!"extract/unsupported: {method.ixName} wants a UInt64 view result for wasm v0"
  unless method.retWidths.isEmpty || method.retWidths.all (· == 8) do
    throw s!"extract/unsupported: {method.ixName} wants a UInt64 view result for wasm v0"
  unless method.retCount == 1 do
    throw s!"extract/unsupported: {method.ixName} view result count {method.retCount} is out of range; wasm v0 wants exactly one"

/-- Lower an already projected and target-bound source program into the shared WASM physical
shape. Chain adapters may rewrite logical boundary parameters before this gate; all resulting
values and operations must still satisfy the narrow WASM family subset below. -/
def fromProjected {ValExt : Type} [BEq ValExt] {OpExt : Type → Type}
    (source : Core.IR.Program ValExt OpExt) : Except String (Program ValExt OpExt) := do
  if source.slots.isEmpty then
    throw "extract/unsupported: wasm program has no slots"
  for slot in source.slots do
    unless slot.width == 8 do
      throw s!"extract/unsupported: wasm v0 wants UInt64 state {slot.name}, got width {slot.width}"
  let mut initializer? : Option (Core.IR.Method ValExt OpExt) := none
  let mut sources : Array (Core.IR.Method ValExt OpExt) := #[]
  for method in source.methods do
    checkParams method
    let ops ←
      match lowerOps method.ops with
      | .ok ops => pure ops
      | .error reason => throw s!"{method.ixName}: {reason}"
    let method := { method with ops }
    unless method.ops.all opAllowed do
      throw s!"extract/unsupported: {method.ixName} uses an op outside the wasm v0 subset"
    if method.kind == .init then
      if initializer?.isSome then
        throw "extract/unsupported: wasm wants exactly one initializer"
      unless method.ops.any (fun | .returnState _ => true | _ => false) do
        throw "extract/unsupported: wasm init missing returnState"
      initializer? := some method
    else
      sources := sources.push method
  let some initSrc := initializer? | throw "extract/unsupported: wasm wants an initializer"
  if sources.isEmpty then
    throw "extract/unsupported: wasm wants at least one entry"
  let init : Method ValExt OpExt := {
    kind := initSrc.kind
    name := initSrc.name
    ixName := initSrc.ixName
    paramCount := initSrc.paramCount
    inputSchema := none
    inputPolicy := ""
    outputSchema := none
    outputPolicy := ""
    tupleArity := none
    ops := initSrc.ops
    evaluation := initSrc.evaluation
  }
  let mut entries : Array (Method ValExt OpExt) := #[]
  for m in sources do
    if m.kind == .get then
      checkViewReturn m
      if hasFallible m.ops then
        throw s!"extract/unsupported: {m.ixName} view must be infallible for wasm v0"
    let tupleArity := if m.kind == .get then some m.retCount else none
    let echoDropped := m.kind != .get && !m.retTypes.isEmpty
    entries := entries.push {
      kind := m.kind
      name := m.name
      ixName := m.ixName
      paramCount := m.paramCount
      inputSchema := none
      inputPolicy := ""
      outputSchema := none
      outputPolicy := ""
      tupleArity
      echoDropped
      ops := m.ops
      evaluation := m.evaluation
    }
  return {
    name := source.name
    slots := source.slots
    initializer := init
    entries
  }

/-- Project the combined extractor dialect through one chain's registration and lower it into the
shared wasm-family physical program. Targets with a non-scalar boundary first project explicitly,
bind that boundary in their own IR module, and call `fromProjected`. -/
def fromExtracted {ValExt : Type} [BEq ValExt] {OpExt : Type → Type}
    (registration : Core.Target.Registration Extract.IR.ValKind Extract.IR.OpExt ValExt OpExt)
    (src : Extract.IR.Program) : Except String (Program ValExt OpExt) := do
  for method in src.methods do
    unless method.annotations.isEmpty do
      throw s!"extract/unsupported: wasm cannot consume target annotations on {method.ixName}"
  let source ← Core.Target.projectProgram registration src
  fromProjected source

/-! ## Canonical digest

The domain is chain-owned and passed in (`Host.Contract.digestDomain`); the spelling
below is shared. Chain dialect extension leaves are spelled through the chain's
`extValCanon` / `extOpCanon` tags so a future host-capability leaf changes only its
own chain's digest deterministically. -/

private def cmpTag : Cmp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt"
  | .le => "le" | .gt => "gt" | .ge => "ge"

partial def valCanon {ValExt : Type} (extValCanon : ValExt → String) :
    Val ValExt → String
  | .arg i => s!"a{i}"
  | .local i => s!"v{i}"
  | .lit n => s!"l{n.toNat}"
  | .field base name => s!"f.{name}({valCanon extValCanon base})"
  | .bitAnd lhs rhs => s!"and({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
  | .bitOr lhs rhs => s!"or({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
  | .bitXor lhs rhs => s!"xor({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
  | .bitNot value => s!"not({valCanon extValCanon value})"
  | .shiftL lhs rhs => s!"shl({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
  | .shiftR lhs rhs => s!"shr({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
  | .indexGet base name idx len off =>
      s!"idx.{name}[{valCanon extValCanon idx}/{len}+{off}]({valCanon extValCanon base})"
  | .loopIx => "ix"
  | .select cmp lhs rhs thn els =>
      s!"sel.{cmpTag cmp}({valCanon extValCanon lhs},{valCanon extValCanon rhs},{valCanon extValCanon thn},{valCanon extValCanon els})"
  | .addU64 lhs rhs => s!"uadd({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
  | .subU64 lhs rhs => s!"usub({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
  | .mulU64 lhs rhs => s!"umul({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
  | .divU64 lhs rhs => s!"udiv({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
  | .modU64 lhs rhs => s!"umod({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
  | .ext kind operands =>
      s!"{extValCanon kind}({String.intercalate "," (operands.map (valCanon extValCanon)).toList})"

partial def opsCanon {ValExt : Type} {OpExt : Type → Type}
    (extValCanon : ValExt → String) (extOpCanon : OpExt (Val ValExt) → String)
    (ops : Array (Op ValExt OpExt)) : String :=
  let rec one (op : Op ValExt OpExt) : String :=
    match op with
    | .letLocal i value => s!"let.{i}({valCanon extValCanon value})"
    | .joinLocal i => s!"join.{i}"
    | .setLocal i value => s!"set.{i}({valCanon extValCanon value})"
    | .checkedAddU64 lhs rhs => s!"add({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
    | .checkedSubU64 lhs rhs => s!"sub({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
    | .checkedMulU64 lhs rhs => s!"mul({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
    | .checkedDivU64 lhs rhs => s!"div({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
    | .checkedModU64 lhs rhs => s!"mod({valCanon extValCanon lhs},{valCanon extValCanon rhs})"
    | .ite cmp lhs rhs thn els =>
        s!"ite.{cmpTag cmp}({valCanon extValCanon lhs},{valCanon extValCanon rhs},[{opsCanon extValCanon extOpCanon thn}],[{opsCanon extValCanon extOpCanon els}])"
    | .forAccum n value resultLocal => s!"for.{resultLocal}({n},{valCanon extValCanon value})"
    | .forBody n body => s!"forb({n},[{opsCanon extValCanon extOpCanon body}])"
    | .indexSetLeaf name idx value len leaf =>
        s!"isetl.{name}.{leaf}[{valCanon extValCanon idx}/{len}]({valCanon extValCanon value})"
    | .indexSet name idx value len elemOff =>
        s!"iset.{name}+{elemOff}[{valCanon extValCanon idx}/{len}]({valCanon extValCanon value})"
    | .storeField name value => s!"st.{name}({valCanon extValCanon value})"
    | .okState value => s!"ok({valCanon extValCanon value})"
    | .errorOverflow => "ovf"
    | .errorNamed name => s!"err.{name}"
    | .returnU64 value => s!"retu({valCanon extValCanon value})"
    | .returnState value => s!"rets({valCanon extValCanon value})"
    | .ext payload => extOpCanon payload
  String.intercalate ";" (ops.toList.map one)

private def methodCanon {ValExt : Type} {OpExt : Type → Type}
    (extValCanon : ValExt → String) (extOpCanon : OpExt (Val ValExt) → String)
    (method : Method ValExt OpExt) : String :=
  let tag := match method.tupleArity with
    | some n => s!"view{n}"
    | none => "mut"
  let echo := if method.echoDropped then "echo" else "noecho"
  let input := if method.inputPolicy.isEmpty then "" else s!":{method.inputPolicy}"
  let output := if method.outputPolicy.isEmpty then "" else s!":{method.outputPolicy}"
  s!"{tag}:{method.ixName}:{method.paramCount}:{echo}{input}{output}:[{opsCanon extValCanon extOpCanon method.ops}]"

def canonical {ValExt : Type} {OpExt : Type → Type}
    (digestDomain : String) (extValCanon : ValExt → String)
    (extOpCanon : OpExt (Val ValExt) → String) (p : Program ValExt OpExt) : String :=
  let slots := String.intercalate ","
    (p.slots.map (fun s => s!"{s.name}:{s.width}")).toList
  let entries :=
    (p.entries.qsort (fun a b => a.ixName < b.ixName)).toList.map (methodCanon extValCanon extOpCanon)
  s!"{digestDomain}{p.name}|{slots}|{methodCanon extValCanon extOpCanon p.initializer}|{String.intercalate "/" entries}"

def digestHex {ValExt : Type} {OpExt : Type → Type}
    (digestDomain : String) (extValCanon : ValExt → String)
    (extOpCanon : OpExt (Val ValExt) → String) (p : Program ValExt OpExt) : String :=
  Core.IR.u64Hex (Core.IR.fnv1a64 (canonical digestDomain extValCanon extOpCanon p))

end ProofForge.Wasm.IR
