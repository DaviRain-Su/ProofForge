import ProofForge.Core.Ops

namespace ProofForge.Core.CFG

abbrev BlockId := Nat
abbrev Val (ValExt : Type) := Core.Ops.Val ValExt
abbrev Op (ValExt : Type) (OpExt : Type → Type) := Core.Ops.Op ValExt OpExt

/-- A block destination. Arguments are explicit so future SSA-style lowering does not need phi nodes. -/
structure Edge (ValExt : Type) where
  target : BlockId
  args : Array (Val ValExt) := #[]
  deriving BEq, Repr

/-- Target-neutral exits. Backends decide how these become ABI returns or reverts. -/
inductive Exit (ValExt : Type) where
  | initialize (values : Array (Val ValExt))
  | okState (value : Val ValExt)
  | errorOverflow
  | errorNamed (name : String)
  | returnU64 (value : Val ValExt)
  | returnState (value : Val ValExt)
  deriving BEq, Repr

inductive Checked (ValExt : Type) where
  | addU64 (lhs rhs : Val ValExt)
  | subU64 (lhs rhs : Val ValExt)
  | mulU64 (lhs rhs : Val ValExt)
  | divU64 (lhs rhs : Val ValExt)
  | modU64 (lhs rhs : Val ValExt)
  | forAccum (bound : Nat) (addend : Val ValExt) (resultLocal : Nat)
  deriving BEq, Repr

/-- Every basic block has exactly one explicit control-flow terminator. -/
inductive Terminator (ValExt : Type) where
  | jump (next : Edge ValExt)
  | branch (cmp : Core.Ops.Cmp) (lhs rhs : Val ValExt)
      (thenEdge elseEdge : Edge ValExt)
  | checked (operation : Checked ValExt) (success overflow : Edge ValExt)
  | exit (result : Exit ValExt)
  | unreachable
  deriving BEq, Repr

structure Block (ValExt : Type) (OpExt : Type → Type) where
  id : BlockId
  params : Array Nat := #[]
  instructions : Array (Op ValExt OpExt) := #[]
  terminator : Terminator ValExt

structure Graph (ValExt : Type) (OpExt : Type → Type) where
  entry : BlockId
  blocks : Array (Block ValExt OpExt)

/-- The two operations a target extension must expose to target-neutral CFG passes. -/
structure Dialect (ValExt : Type) (OpExt : Type → Type) where
  mapValues : (Val ValExt → Val ValExt) → OpExt (Val ValExt) → OpExt (Val ValExt)
  values : OpExt (Val ValExt) → Array (Val ValExt)
  payloadEq : OpExt (Val ValExt) → OpExt (Val ValExt) → Bool

def Terminator.successors : Terminator ValExt → Array (Edge ValExt)
  | .jump next => #[next]
  | .branch _ _ _ thenEdge elseEdge => #[thenEdge, elseEdge]
  | .checked _ success overflow => #[success, overflow]
  | .exit _ | .unreachable => #[]

def Graph.block? (graph : Graph ValExt OpExt) (id : BlockId) :
    Option (Block ValExt OpExt) :=
  graph.blocks.find? (·.id == id)

partial def valueLocalIds : Val ValExt → Array Nat
  | .arg _ | .lit _ | .loopIx => #[]
  | .local id => #[id]
  | .field base _ | .bitNot base => valueLocalIds base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs => valueLocalIds lhs ++ valueLocalIds rhs
  | .indexGet base _ index _ _ => valueLocalIds base ++ valueLocalIds index
  | .select _ lhs rhs thenValue elseValue =>
      valueLocalIds lhs ++ valueLocalIds rhs ++ valueLocalIds thenValue ++
        valueLocalIds elseValue
  | .ext _ operands => operands.flatMap valueLocalIds

private partial def opLocalIds (dialect : Dialect ValExt OpExt) :
    Op ValExt OpExt → Array Nat
  | .letLocal id value | .setLocal id value => #[id] ++ valueLocalIds value
  | .joinLocal id => #[id]
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
      valueLocalIds lhs ++ valueLocalIds rhs
  | .ite _ lhs rhs thenOps elseOps =>
      valueLocalIds lhs ++ valueLocalIds rhs ++
        thenOps.flatMap (opLocalIds dialect) ++ elseOps.flatMap (opLocalIds dialect)
  | .forAccum _ addend resultLocal => #[resultLocal] ++ valueLocalIds addend
  | .forBody _ body => body.flatMap (opLocalIds dialect)
  | .indexSetLeaf _ index value _ _ => valueLocalIds index ++ valueLocalIds value
  | .indexSet _ index value _ _ => valueLocalIds index ++ valueLocalIds value
  | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
      valueLocalIds value
  | .errorOverflow | .errorNamed _ => #[]
  | .ext payload => (dialect.values payload).flatMap valueLocalIds

private def firstFreshLocal (dialect : Dialect ValExt OpExt)
    (ops : Array (Op ValExt OpExt)) : Nat :=
  ops.flatMap (opLocalIds dialect) |>.foldl (init := 0) fun next id => max next (id + 1)

private partial def rewriteLoopValue (loopLocal : Nat) : Val ValExt → Val ValExt
  | .arg id => .arg id
  | .local id => .local id
  | .field base name => .field (rewriteLoopValue loopLocal base) name
  | .lit value => .lit value
  | .bitAnd lhs rhs => .bitAnd (rewriteLoopValue loopLocal lhs) (rewriteLoopValue loopLocal rhs)
  | .bitOr lhs rhs => .bitOr (rewriteLoopValue loopLocal lhs) (rewriteLoopValue loopLocal rhs)
  | .bitXor lhs rhs => .bitXor (rewriteLoopValue loopLocal lhs) (rewriteLoopValue loopLocal rhs)
  | .bitNot value => .bitNot (rewriteLoopValue loopLocal value)
  | .shiftL lhs rhs => .shiftL (rewriteLoopValue loopLocal lhs) (rewriteLoopValue loopLocal rhs)
  | .shiftR lhs rhs => .shiftR (rewriteLoopValue loopLocal lhs) (rewriteLoopValue loopLocal rhs)
  | .indexGet base name index len elemOffset =>
      .indexGet (rewriteLoopValue loopLocal base) name (rewriteLoopValue loopLocal index)
        len elemOffset
  | .loopIx => .local loopLocal
  | .select cmp lhs rhs thenValue elseValue =>
      .select cmp (rewriteLoopValue loopLocal lhs) (rewriteLoopValue loopLocal rhs)
        (rewriteLoopValue loopLocal thenValue) (rewriteLoopValue loopLocal elseValue)
  | .addU64 lhs rhs => .addU64 (rewriteLoopValue loopLocal lhs) (rewriteLoopValue loopLocal rhs)
  | .subU64 lhs rhs => .subU64 (rewriteLoopValue loopLocal lhs) (rewriteLoopValue loopLocal rhs)
  | .mulU64 lhs rhs => .mulU64 (rewriteLoopValue loopLocal lhs) (rewriteLoopValue loopLocal rhs)
  | .divU64 lhs rhs => .divU64 (rewriteLoopValue loopLocal lhs) (rewriteLoopValue loopLocal rhs)
  | .modU64 lhs rhs => .modU64 (rewriteLoopValue loopLocal lhs) (rewriteLoopValue loopLocal rhs)
  | .ext kind operands => .ext kind (operands.map (rewriteLoopValue loopLocal))

private partial def mapOpValues (dialect : Dialect ValExt OpExt)
    (mapValue : Val ValExt → Val ValExt) : Op ValExt OpExt → Op ValExt OpExt
  | .letLocal id value => .letLocal id (mapValue value)
  | .joinLocal id => .joinLocal id
  | .setLocal id value => .setLocal id (mapValue value)
  | .checkedAddU64 lhs rhs => .checkedAddU64 (mapValue lhs) (mapValue rhs)
  | .checkedSubU64 lhs rhs => .checkedSubU64 (mapValue lhs) (mapValue rhs)
  | .checkedMulU64 lhs rhs => .checkedMulU64 (mapValue lhs) (mapValue rhs)
  | .checkedDivU64 lhs rhs => .checkedDivU64 (mapValue lhs) (mapValue rhs)
  | .checkedModU64 lhs rhs => .checkedModU64 (mapValue lhs) (mapValue rhs)
  | .ite cmp lhs rhs thenOps elseOps =>
      .ite cmp (mapValue lhs) (mapValue rhs)
        (thenOps.map (mapOpValues dialect mapValue))
        (elseOps.map (mapOpValues dialect mapValue))
  | .forAccum bound addend resultLocal => .forAccum bound (mapValue addend) resultLocal
  | .forBody bound body => .forBody bound (body.map (mapOpValues dialect mapValue))
  | .indexSetLeaf name index value len leaf =>
      .indexSetLeaf name (mapValue index) (mapValue value) len leaf
  | .indexSet name index value len elemOffset =>
      .indexSet name (mapValue index) (mapValue value) len elemOffset
  | .storeField name value => .storeField name (mapValue value)
  | .okState value => .okState (mapValue value)
  | .errorOverflow => .errorOverflow
  | .errorNamed name => .errorNamed name
  | .returnU64 value => .returnU64 (mapValue value)
  | .returnState value => .returnState (mapValue value)
  | .ext payload => .ext (dialect.mapValues mapValue payload)

private partial def rewriteLoopOp (dialect : Dialect ValExt OpExt) (loopLocal : Nat) :
    Op ValExt OpExt → Op ValExt OpExt
  | .forAccum bound addend resultLocal => .forAccum bound addend resultLocal
  | .forBody bound body => .forBody bound body
  | .ite cmp lhs rhs thenOps elseOps =>
      .ite cmp (rewriteLoopValue loopLocal lhs) (rewriteLoopValue loopLocal rhs)
        (thenOps.map (rewriteLoopOp dialect loopLocal))
        (elseOps.map (rewriteLoopOp dialect loopLocal))
  | op => mapOpValues dialect (rewriteLoopValue loopLocal) op

private structure Builder (ValExt : Type) (OpExt : Type → Type) where
  slots : Array (Option (Block ValExt OpExt)) := #[]
  nextLocal : Nat

private def freshBlock (builder : Builder ValExt OpExt) : BlockId × Builder ValExt OpExt :=
  let id := builder.slots.size
  (id, { builder with slots := builder.slots.push none })

private def freshLocal (builder : Builder ValExt OpExt) : Nat × Builder ValExt OpExt :=
  (builder.nextLocal, { builder with nextLocal := builder.nextLocal + 1 })

private def setBlock (builder : Builder ValExt OpExt) (block : Block ValExt OpExt) :
    Except String (Builder ValExt OpExt) :=
  if block.id < builder.slots.size then
    pure { builder with slots := builder.slots.set! block.id (some block) }
  else
    throw s!"cfg/internal: block {block.id} was not allocated"

private def edge (target : BlockId) : Edge ValExt := { target }

mutual
  private partial def lowerRegion (dialect : Dialect ValExt OpExt)
      (ops : Array (Op ValExt OpExt)) (fallback : Terminator ValExt)
      (builder : Builder ValExt OpExt) :
      Except String (BlockId × Builder ValExt OpExt) := do
    let (id, builder) := freshBlock builder
    let builder ← lowerInto dialect id #[] ops.toList fallback builder
    pure (id, builder)

  private partial def lowerInto (dialect : Dialect ValExt OpExt) (id : BlockId)
      (instructions : Array (Op ValExt OpExt)) (remaining : List (Op ValExt OpExt))
      (fallback : Terminator ValExt) (builder : Builder ValExt OpExt) :
      Except String (Builder ValExt OpExt) := do
    match remaining with
    | [] => setBlock builder { id, instructions, terminator := fallback }
    | .checkedAddU64 lhs rhs :: rest =>
        lowerChecked dialect id instructions (.addU64 lhs rhs) rest fallback builder
    | .checkedSubU64 lhs rhs :: rest =>
        lowerChecked dialect id instructions (.subU64 lhs rhs) rest fallback builder
    | .checkedMulU64 lhs rhs :: rest =>
        lowerChecked dialect id instructions (.mulU64 lhs rhs) rest fallback builder
    | .checkedDivU64 lhs rhs :: rest =>
        lowerChecked dialect id instructions (.divU64 lhs rhs) rest fallback builder
    | .checkedModU64 lhs rhs :: rest =>
        lowerChecked dialect id instructions (.modU64 lhs rhs) rest fallback builder
    | .forAccum bound addend resultLocal :: rest =>
        lowerChecked dialect id instructions (.forAccum bound addend resultLocal)
          rest fallback builder
    | .ite cmp lhs rhs thenOps elseOps :: rest =>
        let (continuation, builder) ← lowerRegion dialect rest.toArray fallback builder
        let (thenBlock, builder) ←
          lowerRegion dialect thenOps (.jump (edge continuation)) builder
        let (elseBlock, builder) ←
          lowerRegion dialect elseOps (.jump (edge continuation)) builder
        setBlock builder {
          id
          instructions
          terminator := .branch cmp lhs rhs (edge thenBlock) (edge elseBlock)
        }
    | .forBody bound body :: rest =>
        let (continuation, builder) ← lowerRegion dialect rest.toArray fallback builder
        let (loopLocal, builder) := freshLocal builder
        let (header, builder) := freshBlock builder
        let (latch, builder) := freshBlock builder
        let rewrittenBody := body.map (rewriteLoopOp dialect loopLocal)
        let (bodyBlock, builder) ←
          lowerRegion dialect rewrittenBody (.jump (edge latch)) builder
        let builder ← setBlock builder {
          id
          instructions := instructions.push (.letLocal loopLocal (.lit 0))
          terminator := .jump (edge header)
        }
        let builder ← setBlock builder {
          id := header
          terminator := .branch .lt (.local loopLocal) (.lit (UInt64.ofNat bound))
            (edge bodyBlock) (edge continuation)
        }
        setBlock builder {
          id := latch
          instructions := #[.setLocal loopLocal (.addU64 (.local loopLocal) (.lit 1))]
          terminator := .jump (edge header)
        }
    | .okState value :: rest => finishExit id instructions (.okState value) rest builder
    | .errorOverflow :: rest => finishExit id instructions .errorOverflow rest builder
    | .errorNamed name :: rest => finishExit id instructions (.errorNamed name) rest builder
    | .returnU64 value :: rest => finishExit id instructions (.returnU64 value) rest builder
    | .returnState value :: rest => finishExit id instructions (.returnState value) rest builder
    | op :: rest => lowerInto dialect id (instructions.push op) rest fallback builder

  private partial def lowerChecked (dialect : Dialect ValExt OpExt) (id : BlockId)
      (instructions : Array (Op ValExt OpExt)) (operation : Checked ValExt)
      (remaining : List (Op ValExt OpExt)) (fallback : Terminator ValExt)
      (builder : Builder ValExt OpExt) : Except String (Builder ValExt OpExt) := do
    let (success, builder) ← lowerRegion dialect remaining.toArray fallback builder
    let (overflow, builder) ←
      lowerRegion dialect #[] (.exit .errorOverflow) builder
    setBlock builder { id, instructions, terminator := .checked operation (edge success) (edge overflow) }

  private partial def finishExit (id : BlockId)
      (instructions : Array (Op ValExt OpExt)) (result : Exit ValExt)
      (remaining : List (Op ValExt OpExt)) (builder : Builder ValExt OpExt) :
      Except String (Builder ValExt OpExt) := do
    unless remaining.all fun
        | .okState _ | .errorOverflow | .errorNamed _ | .returnU64 _ | .returnState _ => true
        | _ => false do
      throw s!"cfg/invalid: instructions follow terminal operation in block {id}"
    setBlock builder { id, instructions, terminator := .exit result }
end

private def instructionAllowed : Op ValExt OpExt → Bool
  | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
  | .checkedDivU64 .. | .checkedModU64 .. | .forAccum ..
  | .ite .. | .forBody .. | .okState _ | .errorOverflow | .errorNamed _
  | .returnU64 _ | .returnState _ => false
  | _ => true

private partial def reachableFrom (graph : Graph ValExt OpExt)
    (pending : List BlockId) (seen : Array BlockId) : Array BlockId :=
  match pending with
  | [] => seen
  | id :: rest =>
      if seen.contains id then
        reachableFrom graph rest seen
      else
        match graph.block? id with
        | none => reachableFrom graph rest (seen.push id)
        | some block =>
            let next := block.terminator.successors.toList.map (·.target)
            reachableFrom graph (next ++ rest) (seen.push id)

def Graph.reachable (graph : Graph ValExt OpExt) : Array BlockId :=
  reachableFrom graph [graph.entry] #[]

def Graph.pruneUnreachable (graph : Graph ValExt OpExt) : Graph ValExt OpExt :=
  let reachable := graph.reachable
  { graph with blocks := graph.blocks.filter (reachable.contains ·.id) }

/-- Check the invariants relied on by later optimization and code-generation passes. -/
def Graph.validate (graph : Graph ValExt OpExt) : Except String Unit := do
  unless graph.blocks.any (·.id == graph.entry) do
    throw s!"cfg/invalid: missing entry block {graph.entry}"
  let ids := graph.blocks.map (·.id)
  unless ids.size == ids.toList.eraseDups.length do
    throw "cfg/invalid: duplicate block id"
  for block in graph.blocks do
    unless block.instructions.all instructionAllowed do
      throw s!"cfg/invalid: structured control or exit remains in block {block.id}"
    unless block.params.size == block.params.toList.eraseDups.length do
      throw s!"cfg/invalid: duplicate parameter in block {block.id}"
    match block.terminator with
    | .unreachable => throw s!"cfg/invalid: reachable incomplete block {block.id}"
    | _ => pure ()
    for next in block.terminator.successors do
      match graph.block? next.target with
      | none => throw s!"cfg/invalid: block {block.id} jumps to missing block {next.target}"
      | some target =>
          unless next.args.size == target.params.size do
            throw (s!"cfg/invalid: edge {block.id} -> {target.id} passes {next.args.size} " ++
              s!"arguments to {target.params.size} parameters")
  let reachable := graph.reachable
  unless reachable.size == graph.blocks.size do
    throw "cfg/invalid: graph contains unreachable blocks"

/-- Convert structured control and checked operations to explicit blocks and edges. Checked
accumulation retains its bounded operation payload but exposes success/overflow successors. -/
def lower (dialect : Dialect ValExt OpExt) (ops : Array (Op ValExt OpExt)) :
    Except String (Graph ValExt OpExt) := do
  let builder : Builder ValExt OpExt := { nextLocal := firstFreshLocal dialect ops }
  let (entry, builder) ← lowerRegion dialect ops .unreachable builder
  let blocks ← builder.slots.mapM fun
    | some block => pure block
    | none => throw "cfg/internal: allocated block was not completed"
  let graph := ({ entry, blocks } : Graph ValExt OpExt).pruneUnreachable
  graph.validate
  pure graph

/-- Initializers encode one output value per state leaf as repeated `returnState` operations. Their
effects still use the normal CFG, but the collected state vector is one deployment-only exit. -/
def lowerInit (dialect : Dialect ValExt OpExt) (ops : Array (Op ValExt OpExt)) :
    Except String (Graph ValExt OpExt) := do
  let values := ops.filterMap fun
    | .returnState value => some value
    | _ => none
  unless !values.isEmpty do
    throw "cfg/invalid: initializer has no state values"
  let effects := ops.filter fun
    | .returnState _ => false
    | _ => true
  let builder : Builder ValExt OpExt := { nextLocal := firstFreshLocal dialect ops }
  let (entry, builder) ← lowerRegion dialect effects (.exit (.initialize values)) builder
  let blocks ← builder.slots.mapM fun
    | some block => pure block
    | none => throw "cfg/internal: allocated block was not completed"
  let graph := ({ entry, blocks } : Graph ValExt OpExt).pruneUnreachable
  graph.validate
  pure graph

private partial def substituteValue (substitutions : Array (Nat × Val ValExt))
    (fuel : Nat) : Val ValExt → Val ValExt
  | .local id =>
      match fuel with
      | 0 => .local id
      | fuel + 1 =>
          match substitutions.foldl (init := none) fun found entry =>
              if entry.1 == id then some entry.2 else found with
          | some value => substituteValue substitutions fuel value
          | none => .local id
  | .field base name => .field (substituteValue substitutions fuel base) name
  | .bitAnd lhs rhs => .bitAnd (substituteValue substitutions fuel lhs)
      (substituteValue substitutions fuel rhs)
  | .bitOr lhs rhs => .bitOr (substituteValue substitutions fuel lhs)
      (substituteValue substitutions fuel rhs)
  | .bitXor lhs rhs => .bitXor (substituteValue substitutions fuel lhs)
      (substituteValue substitutions fuel rhs)
  | .bitNot value => .bitNot (substituteValue substitutions fuel value)
  | .shiftL lhs rhs => .shiftL (substituteValue substitutions fuel lhs)
      (substituteValue substitutions fuel rhs)
  | .shiftR lhs rhs => .shiftR (substituteValue substitutions fuel lhs)
      (substituteValue substitutions fuel rhs)
  | .indexGet base name index len elemOffset =>
      .indexGet (substituteValue substitutions fuel base) name
        (substituteValue substitutions fuel index) len elemOffset
  | .select cmp lhs rhs thenValue elseValue =>
      .select cmp (substituteValue substitutions fuel lhs)
        (substituteValue substitutions fuel rhs) (substituteValue substitutions fuel thenValue)
        (substituteValue substitutions fuel elseValue)
  | .addU64 lhs rhs => .addU64 (substituteValue substitutions fuel lhs)
      (substituteValue substitutions fuel rhs)
  | .subU64 lhs rhs => .subU64 (substituteValue substitutions fuel lhs)
      (substituteValue substitutions fuel rhs)
  | .mulU64 lhs rhs => .mulU64 (substituteValue substitutions fuel lhs)
      (substituteValue substitutions fuel rhs)
  | .divU64 lhs rhs => .divU64 (substituteValue substitutions fuel lhs)
      (substituteValue substitutions fuel rhs)
  | .modU64 lhs rhs => .modU64 (substituteValue substitutions fuel lhs)
      (substituteValue substitutions fuel rhs)
  | .ext kind operands => .ext kind (operands.map (substituteValue substitutions fuel))
  | value => value

private partial def cseCandidate : Val ValExt → Bool
  | .arg _ | .local _ | .lit _ => true
  | .field base _ | .bitNot base => cseCandidate base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs => cseCandidate lhs && cseCandidate rhs
  | .indexGet base _ index _ _ => cseCandidate base && cseCandidate index
  | .select _ lhs rhs thenValue elseValue =>
      cseCandidate lhs && cseCandidate rhs && cseCandidate thenValue && cseCandidate elseValue
  | .loopIx | .ext _ _ => false

private def rewriteExit (rewrite : Val ValExt → Val ValExt) : Exit ValExt → Exit ValExt
  | .initialize values => .initialize (values.map rewrite)
  | .okState value => .okState (rewrite value)
  | .returnU64 value => .returnU64 (rewrite value)
  | .returnState value => .returnState (rewrite value)
  | .errorOverflow => .errorOverflow
  | .errorNamed name => .errorNamed name

private def rewriteTerminator (rewrite : Val ValExt → Val ValExt) :
    Terminator ValExt → Terminator ValExt
  | .jump next => .jump { next with args := next.args.map rewrite }
  | .branch cmp lhs rhs thenEdge elseEdge =>
      .branch cmp (rewrite lhs) (rewrite rhs)
        { thenEdge with args := thenEdge.args.map rewrite }
        { elseEdge with args := elseEdge.args.map rewrite }
  | .checked operation success overflow =>
      let operation := match operation with
        | .addU64 lhs rhs => .addU64 (rewrite lhs) (rewrite rhs)
        | .subU64 lhs rhs => .subU64 (rewrite lhs) (rewrite rhs)
        | .mulU64 lhs rhs => .mulU64 (rewrite lhs) (rewrite rhs)
        | .divU64 lhs rhs => .divU64 (rewrite lhs) (rewrite rhs)
        | .modU64 lhs rhs => .modU64 (rewrite lhs) (rewrite rhs)
        | .forAccum bound addend resultLocal => .forAccum bound (rewrite addend) resultLocal
      .checked operation { success with args := success.args.map rewrite }
        { overflow with args := overflow.args.map rewrite }
  | .exit result => .exit (rewriteExit rewrite result)
  | .unreachable => .unreachable

private def checkedLocalIds : Checked ValExt → Array Nat
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs => valueLocalIds lhs ++ valueLocalIds rhs
  | .forAccum _ addend resultLocal => #[resultLocal] ++ valueLocalIds addend

private def exitLocalIds : Exit ValExt → Array Nat
  | .initialize values => values.flatMap valueLocalIds
  | .okState value | .returnU64 value | .returnState value => valueLocalIds value
  | .errorOverflow | .errorNamed _ => #[]

private def terminatorLocalIds : Terminator ValExt → Array Nat
  | .jump next => next.args.flatMap valueLocalIds
  | .branch _ lhs rhs thenEdge elseEdge =>
      valueLocalIds lhs ++ valueLocalIds rhs ++ thenEdge.args.flatMap valueLocalIds ++
        elseEdge.args.flatMap valueLocalIds
  | .checked operation success overflow =>
      checkedLocalIds operation ++ success.args.flatMap valueLocalIds ++
        overflow.args.flatMap valueLocalIds
  | .exit result => exitLocalIds result
  | .unreachable => #[]

private def blockLocalIds (dialect : Dialect ValExt OpExt) (block : Block ValExt OpExt) :
    Array Nat :=
  block.instructions.flatMap (opLocalIds dialect) ++ terminatorLocalIds block.terminator

private def cseBlock [BEq ValExt] (dialect : Dialect ValExt OpExt)
    (externalLocals : Array Nat)
    (block : Block ValExt OpExt) : Block ValExt OpExt := Id.run do
  let mut instructions := #[]
  let mut available : Array (Val ValExt × Nat) := #[]
  let mut substitutions : Array (Nat × Val ValExt) := #[]
  let mutableLocals := block.instructions.filterMap fun
    | .setLocal id _ | .joinLocal id | .forAccum _ _ id => some id
    | _ => none
  for instruction in block.instructions do
    let rewrite := substituteValue substitutions (substitutions.size + 1)
    match instruction with
    | .letLocal id value =>
        let value := rewrite value
        substitutions := substitutions.filter (·.1 != id)
        available := available.filter (·.2 != id)
        if cseCandidate value then
          match available.find? (·.1 == value) with
          | some previous =>
              if !externalLocals.contains id && !mutableLocals.contains previous.2 &&
                  (valueLocalIds value).all (!mutableLocals.contains ·) then
                substitutions := substitutions.push (id, .local previous.2)
              else
                instructions := instructions.push (.letLocal id value)
                available := available.push (value, id)
          | none =>
              instructions := instructions.push (.letLocal id value)
              available := available.push (value, id)
        else
          instructions := instructions.push (.letLocal id value)
    | .setLocal id value =>
        instructions := instructions.push (.setLocal id (rewrite value))
        substitutions := substitutions.filter (·.1 != id)
        available := #[]
    | .joinLocal id =>
        instructions := instructions.push (mapOpValues dialect rewrite instruction)
        substitutions := substitutions.filter (·.1 != id)
        available := #[]
    | .forAccum _ _ resultLocal =>
        instructions := instructions.push (mapOpValues dialect rewrite instruction)
        substitutions := substitutions.filter (·.1 != resultLocal)
        available := #[]
    | .storeField .. | .indexSet .. | .indexSetLeaf .. | .ext _ =>
        instructions := instructions.push (mapOpValues dialect rewrite instruction)
        available := #[]
    | _ => instructions := instructions.push (mapOpValues dialect rewrite instruction)
  let rewrite := substituteValue substitutions (substitutions.size + 1)
  return { block with
    instructions
    terminator := rewriteTerminator rewrite block.terminator
  }

/-- Scope-local CSE. It never crosses a block or reorders effects, and invalidates state reads at
every memory/target-effect barrier. -/
def localCSE [BEq ValExt] (dialect : Dialect ValExt OpExt)
    (graph : Graph ValExt OpExt) : Graph ValExt OpExt := Id.run do
  let mut ownership : Array (Nat × Array BlockId) := #[]
  for block in graph.blocks do
    for id in (blockLocalIds dialect block).toList.eraseDups do
      match ownership.findIdx? (·.1 == id) with
      | some index =>
          let entry := ownership[index]!
          ownership := ownership.set! index (id, entry.2.push block.id)
      | none => ownership := ownership.push (id, #[block.id])
  return { graph with
    blocks := graph.blocks.map fun block =>
      let external := ownership.filterMap fun entry =>
        if entry.2.any (· != block.id) then some entry.1 else none
      cseBlock dialect external block
  }

private def redirectEdge (redirects : Array (BlockId × BlockId)) (next : Edge ValExt) :
    Edge ValExt :=
  let target := redirects.foldl (init := next.target) fun target redirect =>
    if redirect.1 == target then redirect.2 else target
  { next with target }

private def redirectTerminator (redirects : Array (BlockId × BlockId)) :
    Terminator ValExt → Terminator ValExt
  | .jump next => .jump (redirectEdge redirects next)
  | .branch cmp lhs rhs thenEdge elseEdge =>
      .branch cmp lhs rhs (redirectEdge redirects thenEdge) (redirectEdge redirects elseEdge)
  | .checked operation success overflow =>
      .checked operation (redirectEdge redirects success) (redirectEdge redirects overflow)
  | .exit result => .exit result
  | .unreachable => .unreachable

private partial def instructionEq [BEq ValExt] (dialect : Dialect ValExt OpExt) :
    Op ValExt OpExt → Op ValExt OpExt → Bool
  | .letLocal leftId left, .letLocal rightId right => leftId == rightId && left == right
  | .joinLocal left, .joinLocal right => left == right
  | .setLocal leftId left, .setLocal rightId right => leftId == rightId && left == right
  | .checkedAddU64 l1 l2, .checkedAddU64 r1 r2
  | .checkedSubU64 l1 l2, .checkedSubU64 r1 r2
  | .checkedMulU64 l1 l2, .checkedMulU64 r1 r2
  | .checkedDivU64 l1 l2, .checkedDivU64 r1 r2
  | .checkedModU64 l1 l2, .checkedModU64 r1 r2 => l1 == r1 && l2 == r2
  | .forAccum ln la lr, .forAccum rn ra rr => ln == rn && la == ra && lr == rr
  | .indexSetLeaf ln li lv llen lleaf, .indexSetLeaf rn ri rv rlen rleaf =>
      ln == rn && li == ri && lv == rv && llen == rlen && lleaf == rleaf
  | .indexSet ln li lv llen loff, .indexSet rn ri rv rlen roff =>
      ln == rn && li == ri && lv == rv && llen == rlen && loff == roff
  | .storeField ln lv, .storeField rn rv => ln == rn && lv == rv
  | .ext left, .ext right => dialect.payloadEq left right
  | _, _ => false

private def instructionArraysEq [BEq ValExt] (dialect : Dialect ValExt OpExt)
    (left right : Array (Op ValExt OpExt)) : Bool :=
  left.size == right.size && (List.zip left.toList right.toList).all fun pair =>
    instructionEq dialect pair.1 pair.2

/-- Merge adjacent structurally identical blocks. The adjacency restriction keeps this pass linear
on very large extracted contracts; a later layout pass can provide keyed global block interning. -/
def shareBlocks [BEq ValExt] (dialect : Dialect ValExt OpExt)
    (graph : Graph ValExt OpExt) : Graph ValExt OpExt := Id.run do
  let some entry := graph.block? graph.entry | return graph
  let ordered := #[entry] ++ graph.blocks.filter (·.id != graph.entry)
  let mut kept : Array (Block ValExt OpExt) := #[]
  let mut redirects : Array (BlockId × BlockId) := #[]
  for block in ordered do
    match kept.back? with
    | some prior =>
        if prior.params == block.params &&
            instructionArraysEq dialect prior.instructions block.instructions &&
            prior.terminator == block.terminator then
          redirects := redirects.push (block.id, prior.id)
        else
          kept := kept.push block
    | none => kept := kept.push block
  return {
    entry := graph.entry
    blocks := kept.map fun block =>
      { block with terminator := redirectTerminator redirects block.terminator }
  }

def optimize [BEq ValExt] (dialect : Dialect ValExt OpExt) (graph : Graph ValExt OpExt) :
    Except String (Graph ValExt OpExt) := do
  let graph := shareBlocks dialect (localCSE dialect graph)
  graph.validate
  pure graph

end ProofForge.Core.CFG
