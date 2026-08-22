import SolanaLean.Counter

namespace Tests.Fixtures

/-- 负向：入口类型带 `Nat`。 -/
def usesNat (n : Nat) : Nat := n + 1

/-- 负向：partial。 -/
partial def loops (n : UInt64) : UInt64 :=
  loops n

/-- 负向：sorry。 -/
def usesSorry (s : SolanaLean.Counter.State) : UInt64 :=
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
def wrappingAdd (s : SolanaLean.Counter.State) (delta : UInt64) :
    Except SolanaLean.Counter.Error (SolanaLean.Counter.State × UInt64) :=
  let next := s.value + delta
  .ok ({ value := next }, next)

end Tests.Fixtures
