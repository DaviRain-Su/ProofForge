import ProofForge

namespace Examples.Wide

open ProofForge.Evm.Runtime
open ProofForge.Evm
open ProofForge.Evm.Sdk
open ProofForge.Core.Value

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

@[pf_entry]
def add (_s : State) (a b : UInt256) : UInt256 :=
  WideWord.Source.add256 a b

@[pf_entry]
def sub (_s : State) (a b : UInt256) : UInt256 :=
  WideWord.Source.sub256 a b

@[pf_entry]
def mul (_s : State) (a b : UInt256) : UInt256 :=
  WideWord.Source.mul256 a b

@[pf_entry]
def bitAnd (_s : State) (a b : UInt256) : UInt256 :=
  UInt256.bitAnd a b

@[pf_entry]
def bitOr (_s : State) (a b : UInt256) : UInt256 :=
  UInt256.bitOr a b

@[pf_entry]
def bitXor (_s : State) (a b : UInt256) : UInt256 :=
  UInt256.bitXor a b

@[pf_entry]
def complement (_s : State) (a : UInt256) : UInt256 :=
  UInt256.complement a

@[pf_entry]
def shiftLeft (_s : State) (a : UInt256) (bits : UInt64) : UInt256 :=
  UInt256.shiftLeft a bits

@[pf_entry]
def shiftRight (_s : State) (a : UInt256) (bits : UInt64) : UInt256 :=
  UInt256.shiftRight a bits

@[pf_entry]
def div256 (_s : State) (a b : UInt256) : UInt256 :=
  UInt256.div a b

@[pf_entry]
def mod256 (_s : State) (a b : UInt256) : UInt256 :=
  UInt256.mod a b

@[pf_entry]
def eq256 (_s : State) (a b : UInt256) : Bool :=
  UInt256.eq a b

@[pf_entry]
def lt256 (_s : State) (a b : UInt256) : Bool :=
  UInt256.lt a b

@[pf_entry]
def le256 (_s : State) (a b : UInt256) : Bool :=
  UInt256.le a b

@[pf_entry]
def gt256 (_s : State) (a b : UInt256) : Bool :=
  UInt256.gt a b

@[pf_entry]
def ge256 (_s : State) (a b : UInt256) : Bool :=
  UInt256.ge a b

@[pf_entry]
def echo (_s : State) (a : UInt256) : UInt256 :=
  a

@[pf_entry]
def echo128 (_s : State) (a : UInt128) : UInt128 :=
  a

@[pf_entry]
def echoBytes12 (_s : State) (a : FixedBytes 12) : FixedBytes 12 :=
  a

/-- mutate 入口，让模块有 Except 形状。 -/
@[pf_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.Wide
