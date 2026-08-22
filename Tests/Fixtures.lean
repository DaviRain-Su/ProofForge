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

/-- 负向：state 含 Bool，不是支持的叶子。 -/
structure FlagState where
  value : UInt64
  flag : Bool
  deriving Repr, DecidableEq, Inhabited

def initFlag (initial : UInt64) : FlagState :=
  { value := initial, flag := false }

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

def getFlagValue (s : FlagState) : UInt64 :=
  s.value

def creditFlag (s : FlagState) (delta : UInt64) :
    Except Examples.Counter.Error (FlagState × UInt64) :=
  if s.value ≤ Examples.Counter.u64Max - delta then
    let next := s.value + delta
    .ok ({ value := next, flag := s.flag }, next)
  else
    .error .overflow

end Tests.Fixtures
