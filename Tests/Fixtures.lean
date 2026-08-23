import Examples.Counter

namespace Tests.Fixtures

/-- 负向：入口类型带 `Nat`。 -/
def usesNat (n : Nat) : Nat := n + 1

/-- 负向：partial。 -/
partial def loops (n : UInt64) : UInt64 :=
  loops n

/-- 负向：sorry。 -/
def usesSorry (s : Examples.Counter.State) : UInt64 :=
  sorry

/-- 负向：IO。 -/
def usesIO : IO Unit :=
  pure ()

/-- 负向：extern（无实现，只为属性门）。 -/
@[extern "solana_lean_fixture_extern"]
opaque usesExtern : UInt64 → UInt64

/-- 负向：implemented_by 指向 unsafe。 -/
unsafe def usesImplByImpl (x : UInt64) : UInt64 := x

@[implemented_by usesImplByImpl]
def usesImplBy (x : UInt64) : UInt64 := x

/-- 负向：无保护加法，不能抽出 checkedAdd。 -/
def wrappingAdd (s : Examples.Counter.State) (delta : UInt64) :
    Except Examples.Counter.Error (Examples.Counter.State × UInt64) :=
  let next := s.value + delta
  .ok ({ value := next }, next)

def wrappingSub (s : Examples.Counter.State) (delta : UInt64) :
    Except Examples.Counter.Error (Examples.Counter.State × UInt64) :=
  let next := s.value - delta
  .ok ({ value := next }, next)

def wrappingMul (s : Examples.Counter.State) (factor : UInt64) :
    Except Examples.Counter.Error (Examples.Counter.State × UInt64) :=
  let next := s.value * factor
  .ok ({ value := next }, next)

/-- 负向：state 含 Float，不是支持的叶子。 -/
structure FlagState where
  value : UInt64
  flag : Float
  deriving Repr, Inhabited

def initFlag (initial : UInt64) : FlagState :=
  { value := initial, flag := 0 }

/-- 负向：不定长 Array，不是 Vector。 -/
structure BagState where
  items : Array UInt64
  deriving Repr

def initBag (_seed : UInt64) : BagState :=
  { items := #[] }

def getBagHead (_s : BagState) : UInt64 :=
  0

def setBagHead (s : BagState) (n : UInt64) :
    Except Examples.Counter.Error (BagState × UInt64) :=
  .ok ({ items := #[n] }, n)

/-- 负向：带 payload 的 inductive。 -/
inductive Tagged where
  | wrap (n : UInt64)
  deriving Repr

structure TaggedState where
  tag : Tagged
  deriving Repr

def initTagged (n : UInt64) : TaggedState :=
  { tag := .wrap n }

def getTagged (s : TaggedState) : UInt64 :=
  match s.tag with
  | .wrap n => n

def setTagged (s : TaggedState) (n : UInt64) :
    Except Examples.Counter.Error (TaggedState × UInt64) :=
  .ok ({ tag := .wrap n }, n)

def getFlagValue (s : FlagState) : UInt64 :=
  s.value

def creditFlag (s : FlagState) (delta : UInt64) :
    Except Examples.Counter.Error (FlagState × UInt64) :=
  if s.value ≤ Examples.Counter.u64Max - delta then
    let next := s.value + delta
    .ok ({ value := next, flag := s.flag }, next)
  else
    .error .overflow

/-- 正向：target-neutral value arithmetic inside a state-carrying bounded fold. -/
structure FoldState where
  product : UInt64
  quotient : UInt64
  remainder : UInt64
  deriving Repr, DecidableEq

def initFold (_seed : UInt64) : FoldState :=
  { product := 0, quotient := 0, remainder := 0 }

def runFold (s : FoldState) (lhs rhs : UInt64) :
    Except Examples.Counter.Error (FoldState × UInt64) := Id.run do
  let mut st := s
  for i in [:2] do
    if i = 0 then
      st := { st with product := lhs * rhs }
    else
      st := { st with quotient := lhs / rhs, remainder := lhs % rhs }
  .ok (st, st.product)

def foldProduct (s : FoldState) : UInt64 :=
  s.product

/-- Pure conditional values stay shared instead of duplicating the mutation continuation. -/
structure ChoiceState where
  chosen : UInt64
  deriving Repr, DecidableEq

def initChoice (_seed : UInt64) : ChoiceState :=
  { chosen := 0 }

def choose (s : ChoiceState) (lhs rhs : UInt64) :
    Except Examples.Counter.Error (ChoiceState × UInt64) :=
  let chosen : UInt64 := if lhs < rhs then lhs else rhs
  .ok ({ s with chosen }, chosen)

def getChosen (s : ChoiceState) : UInt64 :=
  s.chosen

/-- A fallible scalar producer with two successful paths and one terminal error. -/
private def chooseBelow (lhs rhs limit : UInt64) : Except Examples.Counter.Error UInt64 :=
  if lhs < limit then .ok lhs
  else if rhs < limit then .ok rhs
  else .error .overflow

attribute [pf_inline] chooseBelow

/-- The successful producer value must join before this mutation continuation. -/
def bindChoice (s : ChoiceState) (lhs rhs limit delta : UInt64) :
    Except Examples.Counter.Error (ChoiceState × UInt64) := do
  let chosen ← chooseBelow lhs rhs limit
  if chosen ≤ Examples.Counter.u64Max - delta then
    let total := chosen + delta
    .ok ({ s with chosen := total }, total)
  else
    .error .overflow

end Tests.Fixtures
