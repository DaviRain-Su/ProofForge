import ProofForge
import Examples.Maybe
import Examples.Tree
import Examples.Window

open Lean Elab Command

namespace Tests.NormalizationSpec

#guard
  ProofForge.Core.PathStep.field "Owner" 0 "before" ==
    ProofForge.Core.PathStep.field "Owner" 0 "after"
#guard
  ProofForge.Core.PathStep.field "Owner" 0 "field" !=
    ProofForge.Core.PathStep.field "Owner" 1 "field"

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

def initDirect (initial : UInt64) : State :=
  { value := initial }

def initWithLet (initial : UInt64) : State :=
  let value := initial
  { value }

def incrementDirect (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if s.value ≤ u64Max - delta then
    let next := s.value + delta
    .ok ({ value := next }, next)
  else
    .error .overflow

def incrementWithLets (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  let current := s.value
  if current ≤ u64Max - delta then
    let next := current + delta
    .ok ({ s with value := next }, next)
  else
    .error .overflow

def getDirect (s : State) : UInt64 :=
  s.value

def getWithLet (s : State) : UInt64 :=
  let value := s.value
  value

private def sameMethodCore (left right : ProofForge.Core.IR.Method) : Bool :=
  left.kind == right.kind &&
    left.paramCount == right.paramCount &&
    left.paramWidths == right.paramWidths &&
    left.retCount == right.retCount &&
    left.ops == right.ops &&
    left.evaluation == right.evaluation

private def sameProgramCore (left right : ProofForge.Core.IR.Program) : Bool :=
  left.slots == right.slots &&
    left.schema == right.schema &&
    left.methods.size == right.methods.size &&
    (left.methods.zip right.methods).all fun pair => sameMethodCore pair.1 pair.2

syntax "#pf_guard_equiv " ident ident ident " == " ident ident ident : command

elab_rules : command
  | `(#pf_guard_equiv $initA:ident $mutA:ident $getA:ident ==
      $initB:ident $mutB:ident $getB:ident) => do
      let initAName ← liftCoreM <| realizeGlobalConstNoOverload initA
      let mutAName ← liftCoreM <| realizeGlobalConstNoOverload mutA
      let getAName ← liftCoreM <| realizeGlobalConstNoOverload getA
      let initBName ← liftCoreM <| realizeGlobalConstNoOverload initB
      let mutBName ← liftCoreM <| realizeGlobalConstNoOverload mutB
      let getBName ← liftCoreM <| realizeGlobalConstNoOverload getB
      let env ← getEnv
      let left ←
        match ProofForge.Extract.extractProgram env initAName mutAName getAName with
        | .ok program => pure program
        | .error reason => throwError s!"left frontend: {reason}"
      let right ←
        match ProofForge.Extract.extractProgram env initBName mutBName getBName with
        | .ok program => pure program
        | .error reason => throwError s!"right frontend: {reason}"
      unless sameProgramCore left right do
        throwError s!"frontend normalization mismatch:\n" ++
          s!"leftOps={repr (left.methods.map (·.ops))}\n" ++
          s!"rightOps={repr (right.methods.map (·.ops))}\n" ++
          s!"leftEval={repr (left.methods.map (·.evaluation))}\n" ++
          s!"rightEval={repr (right.methods.map (·.evaluation))}"

#pf_guard_equiv
  Tests.NormalizationSpec.initDirect
  Tests.NormalizationSpec.incrementDirect
  Tests.NormalizationSpec.getDirect ==
  Tests.NormalizationSpec.initWithLet
  Tests.NormalizationSpec.incrementWithLets
  Tests.NormalizationSpec.getWithLet

elab "#pf_guard_core_evaluation" : command => do
  let env ← getEnv
  let counter ←
    match ProofForge.Extract.extractProgram env ``initDirect ``incrementDirect ``getDirect with
    | .ok program => pure program
    | .error reason => throwError reason
  unless counter.methods.all (·.evaluation.explicit) do
    throwError "extracted methods must carry explicit Core evaluation"
  let some increment := counter.methods.find? (·.kind == .increment)
    | throwError "missing normalized increment"
  let some firstLeaf := counter.schema.leaves[0]?
    | throwError "missing normalized state leaf"
  let incrementCommits := increment.evaluation.commits
  unless incrementCommits.size == 1 do
    throwError s!"unexpected increment evaluation: {repr increment.evaluation}"
  let some commit := incrementCommits[0]?
    | throwError "missing increment commit"
  let some write := commit.writes[0]?
    | throwError "checked increment has no writeback"
  let checkedAdd := match write.value with | .checked .add _ _ => true | _ => false
  unless commit.writes.size == 1 && write.place == firstLeaf.place &&
      checkedAdd && commit.result == write.value do
    throwError s!"checked result/writeback is not explicit: {repr commit}"

  let maybe ←
    match ProofForge.Extract.extractModule env (Name.mkSimple "Examples" |>.str "Maybe") none with
    | .ok program => pure program
    | .error reason => throwError reason
  let some setSome := maybe.methods.find? (·.ixName == "setSome")
    | throwError "missing Maybe.setSome"
  let some (tag, payload) := maybe.schema.firstOption?
    | throwError "missing Maybe Option leaves"
  let some optionCommit := setSome.evaluation.commits[0]?
    | throwError s!"missing Maybe.setSome commit: {repr setSome.evaluation}"
  let some tagWrite := optionCommit.writes[0]?
    | throwError "missing Maybe tag write"
  let some payloadWrite := optionCommit.writes[1]?
    | throwError "missing Maybe payload write"
  unless optionCommit.writes.size == 2 && tagWrite.place == tag.place &&
      payloadWrite.place == payload.place &&
      tagWrite.value == .source (.lit 1) && payloadWrite.value == .source (.arg 0) &&
      optionCommit.result == payloadWrite.value do
    throwError s!"Option writeback is not explicit: {repr optionCommit}"

  let tree ←
    match ProofForge.Extract.extractModule env (Name.mkSimple "Examples" |>.str "Tree") none with
    | .ok program => pure program
    | .error reason => throwError reason
  let some rotate := tree.methods.find? (·.ixName == "rotateLeft")
    | throwError "missing Tree.rotateLeft"
  let some nodes := tree.schema.vector? "nodes"
    | throwError "missing Tree.nodes"
  let dynamicWrites := rotate.evaluation.dynamicWrites
  unless !dynamicWrites.isEmpty &&
      dynamicWrites.all (·.place.vector == nodes.place) &&
      rotate.evaluation.commits.all (·.writes.isEmpty) do
    throwError s!"dynamic vector writes must not invent a static first-slot write: {repr rotate.evaluation}"

#pf_guard_core_evaluation

elab "#pf_guard_tree_schema" : command => do
  let env ← getEnv
  let schema ←
    match ProofForge.Extract.inferSchema env ``Examples.Tree.init with
    | .ok schema => pure schema
    | .error reason => throwError reason
  let some vector := schema.vector? "nodes"
    | throwError "typed schema is missing Tree.nodes"
  let names := schema.vectorElementLeaves vector |>.map (vector.relativeLeafName ·)
  unless schema.rootType == "Examples.Tree.State" &&
      schema.leaves.size == 28 && vector.length == 4 &&
      vector.elementBytes == 48 && vector.elementLeaves == 6 &&
      names == #["left", "right", "parent", "color", "key", "value"] do
    throwError s!"unexpected Tree schema: {repr schema}"

#pf_guard_tree_schema

elab "#pf_guard_target_lowering" : command => do
  let env ← getEnv
  let counter ←
    match ProofForge.Extract.extractProgram env ``initDirect ``incrementDirect ``getDirect with
    | .ok program => pure program
    | .error reason => throwError reason
  let svmCounter ←
    match ProofForge.Svm.IR.fromProgram counter with
    | .ok program => pure program
    | .error reason => throwError reason
  let some increment := counter.methods.find? (·.kind == .increment)
    | throwError "missing normalized increment"
  let some checkedWrite := increment.evaluation.commits[0]? >>= (·.writes[0]?)
    | throwError s!"missing normalized checked write: {repr increment.evaluation}"
  let some fragment :=
      ProofForge.Svm.Solanalib.checkedWriteFragment? svmCounter checkedWrite
    | throwError "Solanalib bridge rejected normalized checked write"
  unless fragment.compute == ProofForge.Svm.Solanalib.checkedArithBody .add &&
      fragment.store == .st .m64 .br6 (.reg .br4) (BitVec.ofNat 16 104) do
    throwError s!"unexpected Solanalib checked-write fragment: {repr fragment}"

  let tree ←
    match ProofForge.Extract.extractModule env (Name.mkSimple "Examples" |>.str "Tree") none with
    | .ok program => pure program
    | .error reason => throwError reason
  let svmTree ←
    match ProofForge.Svm.IR.fromProgram tree with
    | .ok program => pure program
    | .error reason => throwError reason
  let evmTree ←
    match ProofForge.Evm.IR.fromProgram tree with
    | .ok program => pure program
    | .error reason => throwError reason
  let some sourceNodes := tree.schema.vector? "nodes"
    | throwError "missing source Tree.nodes"
  let some svmNodes := svmTree.vectors.find? (·.place == some sourceNodes.place)
    | throwError s!"SVM target IR lost Tree.nodes identity: {repr svmTree.vectors}"
  let some evmNodes := evmTree.vectors.find? (·.place == some sourceNodes.place)
    | throwError s!"EVM target IR lost Tree.nodes identity: {repr evmTree.vectors}"
  let some svmValue := svmNodes.leaves.find? (·.offset == 40)
    | throwError s!"SVM target IR lost nodes[i].value: {repr svmNodes}"
  let some evmValue := evmNodes.leaves.find? (·.byteOffset == 40)
    | throwError s!"EVM target IR lost nodes[i].value: {repr evmNodes}"
  let some rotate := tree.methods.find? (·.ixName == "rotateLeft")
    | throwError "missing Tree.rotateLeft"
  unless svmNodes.baseOffset == 40 && svmNodes.length == 4 && svmNodes.strideBytes == 48 &&
      evmNodes.baseSlot == 4 && evmNodes.length == 4 && evmNodes.strideSlots == 6 &&
      evmValue.slotOffset == 5 && svmValue.elementPath == evmValue.elementPath &&
      !rotate.evaluation.dynamicWrites.isEmpty &&
      rotate.evaluation.dynamicWrites.all fun write =>
        svmNodes.leaves.any (·.elementPath == write.place.elementPath) do
    throwError s!"target vector layout mismatch:\nsvm={repr svmNodes}\nevm={repr evmNodes}"

  let maybe ←
    match ProofForge.Extract.extractModule env (Name.mkSimple "Examples" |>.str "Maybe") none with
    | .ok program => pure program
    | .error reason => throwError reason
  let svmMaybe ←
    match ProofForge.Svm.IR.fromProgram maybe with
    | .ok program => pure program
    | .error reason => throwError reason
  let evmMaybe ←
    match ProofForge.Evm.IR.fromProgram maybe with
    | .ok program => pure program
    | .error reason => throwError reason
  let some (tag, payload) := maybe.schema.firstOption?
    | throwError "missing Maybe Option leaves"
  let svmTag := svmMaybe.slots.find? (·.place == some tag.place)
  let svmPayload := svmMaybe.slots.find? (·.place == some payload.place)
  let evmTag := evmMaybe.slots.find? (·.place == some tag.place)
  let evmPayload := evmMaybe.slots.find? (·.place == some payload.place)
  unless svmTag.map (·.offset) == some 8 && svmPayload.map (·.offset) == some 16 &&
      evmTag.map (·.index) == some 0 && evmPayload.map (·.index) == some 1 do
    throwError s!"target Option layout mismatch:\nsvm={repr svmMaybe.slots}\nevm={repr evmMaybe.slots}"

#pf_guard_target_lowering

private def firstStringDiff (left right : String) : Nat := Id.run do
  let mut index := 0
  for pair in left.toList.zip right.toList do
    if pair.1 != pair.2 then return index
    index := index + 1
  return index

elab "#pf_guard_golden_output " n:ident : command => do
  let env ← getEnv
  let extracted ←
    match ProofForge.Extract.extractModule env n.getId none with
    | .ok program => pure program
    | .error reason => throwError reason
  let some golden := ProofForge.Golden.programs.find? (·.name == extracted.name)
    | throwError s!"missing SVM Golden fixture for {extracted.name}"
  -- Golden fixtures predate module extraction and keep a hand-written method order.
  -- Align that non-semantic order so this guard isolates schema/layout output.
  let extracted := {
    extracted with
    methods := golden.methods.filterMap fun method =>
      extracted.methods.find? (·.ixName == method.ixName)
  }
  unless extracted.methods.size == golden.methods.size do
    throwError s!"method mismatch for {extracted.name}"
  let extractedAsm ←
    match ProofForge.Svm.Emit.emitCounterAsm extracted with
    | .ok asm => pure asm
    | .error reason => throwError reason
  let goldenAsm ←
    match ProofForge.Svm.Emit.emitCounterAsm golden with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless extractedAsm == goldenAsm &&
      ProofForge.Svm.Idl.emitIdl extracted == ProofForge.Svm.Idl.emitIdl golden do
    let index := firstStringDiff extractedAsm goldenAsm
    throwError s!"typed SVM output changed for {extracted.name} at {index}:\n" ++
      s!"typed={repr (extractedAsm.drop index |>.take 120 |>.copy)}\n" ++
      s!"golden={repr (goldenAsm.drop index |>.take 120 |>.copy)}"
  if let some evmGolden := ProofForge.Evm.Golden.programs.find? (·.name == extracted.name) then
    let extractedEvm ←
      match ProofForge.Evm.IR.fromProgram extracted with
      | .ok program => pure program
      | .error reason => throwError reason
    let extractedYul ←
      match ProofForge.Evm.Emit.emitYul extractedEvm with
      | .ok yul => pure yul
      | .error reason => throwError reason
    let goldenYul ←
      match ProofForge.Evm.Emit.emitYul evmGolden with
      | .ok yul => pure yul
      | .error reason => throwError reason
    unless extractedYul == goldenYul &&
        ProofForge.Evm.Emit.emitAbi extractedEvm == ProofForge.Evm.Emit.emitAbi evmGolden do
      let index := firstStringDiff extractedYul goldenYul
      throwError s!"typed EVM output changed for {extracted.name} at {index}:\n" ++
        s!"typed={repr (extractedYul.drop index |>.take 120 |>.copy)}\n" ++
        s!"golden={repr (goldenYul.drop index |>.take 120 |>.copy)}"

#pf_guard_golden_output Examples.Maybe
#pf_guard_golden_output Examples.Window

end Tests.NormalizationSpec
