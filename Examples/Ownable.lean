import ProofForge

namespace Examples.Ownable

open ProofForge.Runtime

/-- owner 三槽 + 一个计数。allowance 走 hashed pair map，不占槽。 -/
structure State where
  owner0 : UInt64
  owner1 : UInt64
  owner2 : UInt64
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  | unauthorized
  deriving Repr, DecidableEq, Inhabited, BEq

/-- pair-key Map 的 hashed base。抽出认这个名字。 -/
def allowBase : UInt64 := 0

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (o0 o1 o2 : UInt64) : State :=
  { owner0 := o0, owner1 := o1, owner2 := o2, value := 0 }

/-- 只有 owner 能加。非 owner → `unauthorized`。 -/
@[pf_entry]
def bump (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if evmCallerW0 = s.owner0 then
    if evmCallerW1 = s.owner1 then
      if evmCallerW2 = s.owner2 then
        if s.value ≤ u64Max - delta then
          let next := s.value + delta
          .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2, value := next }, next)
        else
          .error .overflow
      else
        .error .unauthorized
    else
      .error .unauthorized
  else
    .error .unauthorized

/-- LOG1 `Incremented(uint64)`。 -/
@[pf_entry]
def logInc (_s : State) (amt : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ owner0 := 0, owner1 := 0, owner2 := 0, value := 0 }, evmLogIncremented amt)
  else
    .error .overflow

/-- pair-key `approve(owner, spender) = amt`。 -/
@[pf_entry]
def approve (_s : State) (o0 o1 o2 s0 s1 s2 amt : UInt64) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ owner0 := 0, owner1 := 0, owner2 := 0, value := 0 },
      evmMapSetPair allowBase o0 o1 o2 s0 s1 s2 amt)
  else
    .error .overflow

/-- 把 pair-key 额度写成 `amt`。不是 ERC-20 `transferFrom` 减法。 -/
@[pf_entry]
def spend (_s : State) (o0 o1 o2 s0 s1 s2 amt : UInt64) :
    Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ owner0 := 0, owner1 := 0, owner2 := 0, value := 0 },
      evmMapSetPair allowBase o0 o1 o2 s0 s1 s2 amt)
  else
    .error .overflow

@[pf_entry]
def allowance (_s : State) (o0 o1 o2 s0 s1 s2 : UInt64) : UInt64 :=
  evmMapGetPair allowBase o0 o1 o2 s0 s1 s2

@[pf_entry]
def ownerW0 (s : State) : UInt64 :=
  s.owner0

@[pf_entry]
def ownerW1 (s : State) : UInt64 :=
  s.owner1

@[pf_entry]
def ownerW2 (s : State) : UInt64 :=
  s.owner2

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

end Examples.Ownable
