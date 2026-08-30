import ProofForge

/-!
Extractor regression for one EVM success transition that combines target effects with ordinary
state writes. Mutable target queries needed by those writes are snapshotted first, the effect is
sequenced next, every changed state leaf follows, and exactly one explicit result terminates the
successful branch. This is independent of any SDK container so a future source abstraction cannot
hide a compiler regression.
-/

namespace Tests.EvmEffectStateSpec

open ProofForge.Evm.Sdk
open Lean Elab Command

namespace MixedFixture

structure State where
  items : Vector UInt64 2
  count : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def positions : Storage.U64Map := Storage.Layout.root.u64Map.handle

@[pf_entry]
def init (_seed : UInt64) : State :=
  { items := #v[0, 0], count := 0 }

@[pf_entry]
def countOf (s : State) : UInt64 :=
  s.count

@[pf_entry]
def putAndRecord (s : State) (index key value : UInt64) : Except Error (State × Bool) :=
  if h : index.toNat < 2 then
    .ok ({ s with items := s.items.set index.toNat value h, count := s.count + 1 },
      Effect.thenTrue (positions.put key (s.count + 1)))
  else
    .error .malformed

/-- A map query determines an ordinary Vector write index while the same success transition
clears that map entry. The query must be observed before the target effect, not re-evaluated by
the later Vector store after the clear. -/
@[pf_entry]
def clearAndRecord (s : State) (key value : UInt64) : Except Error (State × Bool) :=
  if h : (positions.get key - 1).toNat < 2 then
    .ok ({ s with
            items := s.items.set (positions.get key - 1).toNat value h,
            count := s.count + 1 },
      Effect.thenTrue (positions.put key 0))
  else
    .error .malformed

end MixedFixture

namespace WideFixture

structure State where
  owner : Address
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { owner := Address.zero }

@[pf_entry]
def ownerOf (s : State) : Address :=
  s.owner

@[pf_entry]
def replaceAndLog (_s : State) (next : Address) (amount : UInt64) :
    Except Error (State × Bool) :=
  if (0 : UInt64) != 1 then
    .ok ({ owner := next }, Effect.thenTrue (Event.transferU64 amount))
  else
    .error .malformed

end WideFixture

private abbrev Op := ProofForge.Extract.IR.Op

private def isMapSet : Op → Bool
  | .ext (.evm (.component (.hashedMap (.setU64 ..)))) => true
  | _ => false

private def isTransferLog : Op → Bool
  | .ext (.evm (.component (.nativeFx (.log "Transfer" _)))) => true
  | _ => false

private def isIndexSet : Op → Bool
  | .indexSetLeaf .. | .indexSet .. => true
  | _ => false

private def isReturn : Op → Bool
  | .returnU64 _ => true
  | _ => false

private partial def hasMapQuery : ProofForge.Extract.IR.Val → Bool
  | .ext (.evm (.component (.hashedMap _))) _ => true
  | .field base _ | .bitNot base => hasMapQuery base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs => hasMapQuery lhs || hasMapQuery rhs
  | .indexGet base _ index _ _ => hasMapQuery base || hasMapQuery index
  | .select _ lhs rhs thn els =>
      hasMapQuery lhs || hasMapQuery rhs || hasMapQuery thn || hasMapQuery els
  | .ext _ operands => operands.any hasMapQuery
  | _ => false

private partial def findSequence (fuel : Nat) (ops : Array Op)
    (predicate : Array Op → Bool) : Option (Array Op) :=
  if predicate ops then some ops
  else match fuel with
    | 0 => none
    | fuel' + 1 => ops.findSome? fun
        | .ite _ _ _ thn els =>
            findSequence fuel' thn predicate <|> findSequence fuel' els predicate
        | .forBody _ body => findSequence fuel' body predicate
        | _ => none

private def storeNames (ops : Array Op) : Array String :=
  ops.filterMap fun
    | .storeField name _ => some name
    | _ => none

private def expectEffectStateMerge : CommandElabM Unit := do
  let env ← getEnv
  let mixed ←
    match ProofForge.Extract.extractModuleIR env `Tests.EvmEffectStateSpec.MixedFixture with
    | .ok program => pure program
    | .error reason => throwError reason
  let some method := mixed.methods.find? (·.ixName == "putAndRecord")
    | throwError "mixed effect/state fixture omitted putAndRecord"
  let some sequence := findSequence 16 method.ops fun ops =>
      ops.any isMapSet && ops.any isIndexSet && storeNames ops == #["count"]
    | throwError "mixed effect/state sequence was not preserved"
  unless (sequence.countP isMapSet) == 1 && (sequence.countP isIndexSet) == 1 &&
      storeNames sequence == #["count"] &&
      (sequence.countP fun | .okState _ => true | _ => false) == 0 &&
      (sequence.countP isReturn) == 1 do
    throwError "mixed effect/state sequence duplicated or lost an operation"
  let some effectIndex := sequence.findIdx? isMapSet
    | throwError "mixed effect/state sequence lost its map effect"
  let some vectorIndex := sequence.findIdx? isIndexSet
    | throwError "mixed effect/state sequence lost its vector write"
  let some scalarIndex := sequence.findIdx? fun | .storeField "count" _ => true | _ => false
    | throwError "mixed effect/state sequence lost its scalar write"
  let some returnIndex := sequence.findIdx? isReturn
    | throwError "mixed effect/state sequence lost its return"
  unless effectIndex < vectorIndex && vectorIndex < scalarIndex && scalarIndex < returnIndex do
    throwError "mixed effect/state ordering drifted"

  let some method := mixed.methods.find? (·.ixName == "clearAndRecord")
    | throwError "mixed effect/state fixture omitted clearAndRecord"
  let some sequence := findSequence 16 method.ops fun ops =>
      ops.any isMapSet && ops.any isIndexSet && storeNames ops == #["count"]
    | throwError "query-indexed effect/state sequence was not preserved"
  let snapshots := sequence.filterMap fun
    | .letLocal index value => if hasMapQuery value then some index else none
    | _ => none
  unless snapshots.size == 1 do
    throwError "mutable EVM query was not snapshotted exactly once before the effect"
  let snapshot := snapshots[0]!
  let some snapshotIndex := sequence.findIdx? fun
      | .letLocal index value => index == snapshot && hasMapQuery value
      | _ => false
    | throwError "mutable EVM query snapshot is missing"
  let some effectIndex := sequence.findIdx? isMapSet
    | throwError "query-indexed sequence lost its map effect"
  let some vectorIndex := sequence.findIdx? fun
      | .indexSetLeaf _ (.local index) _ _ _ | .indexSet _ (.local index) _ _ _ =>
          index == snapshot
      | _ => false
    | throwError "Vector write did not consume the pre-effect query snapshot"
  let some scalarIndex := sequence.findIdx? fun | .storeField "count" _ => true | _ => false
    | throwError "query-indexed sequence lost its scalar write"
  let some returnIndex := sequence.findIdx? isReturn
    | throwError "query-indexed sequence lost its return"
  unless snapshotIndex < effectIndex && effectIndex < vectorIndex &&
      vectorIndex < scalarIndex && scalarIndex < returnIndex do
    throwError "query snapshot/effect/state ordering drifted"

  let wide ←
    match ProofForge.Extract.extractModuleIR env `Tests.EvmEffectStateSpec.WideFixture with
    | .ok program => pure program
    | .error reason => throwError reason
  let some method := wide.methods.find? (·.ixName == "replaceAndLog")
    | throwError "wide effect/state fixture omitted replaceAndLog"
  let some sequence := findSequence 16 method.ops fun ops =>
      ops.any isTransferLog &&
        storeNames ops == #["owner_w0", "owner_w1", "owner_w2"]
    | throwError "wide effect/state sequence was not preserved"
  unless (sequence.countP isTransferLog) == 1 &&
      storeNames sequence == #["owner_w0", "owner_w1", "owner_w2"] &&
      (sequence.countP fun | .okState _ => true | _ => false) == 0 &&
      (sequence.countP isReturn) == 1 do
    throwError "wide effect/state sequence duplicated or lost an operation"
  let some effectIndex := sequence.findIdx? isTransferLog
    | throwError "wide effect/state sequence lost its log effect"
  let some firstStoreIndex := sequence.findIdx? fun | .storeField _ _ => true | _ => false
    | throwError "wide effect/state sequence lost its owner write"
  let some returnIndex := sequence.findIdx? isReturn
    | throwError "wide effect/state sequence lost its return"
  unless effectIndex < firstStoreIndex && firstStoreIndex < returnIndex do
    throwError "wide effect/state ordering drifted"

elab "#pf_guard_evm_effect_state" : command => expectEffectStateMerge

#pf_guard_evm_effect_state

end Tests.EvmEffectStateSpec
