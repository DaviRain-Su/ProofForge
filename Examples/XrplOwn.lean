import ProofForge

namespace Examples.XrplOwn

open ProofForge.Wasm.Xrpl.Runtime

/-- owner 是三叶 AccountId，不是 8 字节身份。value 只有 owner 能改。 -/
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

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- 把当前 `ContractCall` 的 caller 三叶写成 owner。 -/
@[pf_entry]
def init (_seed : UInt64) : State :=
  { owner0 := xrplCallerW0, owner1 := xrplCallerW1, owner2 := xrplCallerW2, value := 0 }

/-- 三叶全等才加 1。嵌套 `if`，不用 `&&`（那会变成 wasm v0 拒掉的 `bitAnd`）。 -/
@[pf_entry]
def bump (s : State) : Except Error (State × UInt64) :=
  if xrplCallerW0 = s.owner0 then
    if xrplCallerW1 = s.owner1 then
      if xrplCallerW2 = s.owner2 then
        if s.value ≤ u64Max - 1 then
          -- Public result is dropped on the status ABI; a shared `let next` becomes
          -- wasm-v0-rejected `letLocal`. Write the slot, return a literal.
          .ok ({ owner0 := s.owner0, owner1 := s.owner1, owner2 := s.owner2,
                 value := s.value + 1 }, (0 : UInt64))
        else
          .error .overflow
      else
        .error .unauthorized
    else
      .error .unauthorized
  else
    .error .unauthorized

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

@[pf_entry]
def ownerLo (s : State) : UInt64 :=
  s.owner0

end Examples.XrplOwn
