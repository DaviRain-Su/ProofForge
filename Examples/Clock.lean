import ProofForge

namespace Examples.Clock

open ProofForge.Svm.Sdk

structure State where
  stamped : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { stamped := 0 }

/-- view：当前物理 slot。宿主侧是 stub；链上走 `sol_get_clock_sysvar`。 -/
@[pf_entry]
def height (_s : State) : UInt64 :=
  Sysvar.Clock.slot

/-- view：当前 epoch。同一条 Clock sysvar，读偏移 16。 -/
@[pf_entry]
def era (_s : State) : UInt64 :=
  Sysvar.Clock.epoch

/-- view：最近完成 leader schedule 计算的 future epoch。 -/
@[pf_entry]
def leaderEra (_s : State) : UInt64 :=
  Sysvar.Clock.leaderScheduleEpoch

/-- view：账户 0 公钥的第一个小端 u64。入口会要求 signer。 -/
@[pf_entry]
def key0 (_s : State) : UInt64 :=
  ProofForge.Svm.Runtime.signerKey0

/-- 把当前 slot 写入状态。`0 ≠ 1` 给无参 mutate 一条比较守卫。 -/
@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Sysvar.Clock.slot }, Sysvar.Clock.slot)
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.stamped

end Examples.Clock
