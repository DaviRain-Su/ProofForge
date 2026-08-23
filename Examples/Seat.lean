import ProofForge

/-!
席位 PDA + 双 vault 初始化。不跟 Phoenix 挂单/吃单混：
CPI 账户表不同，混在一个 Program 会抬高 `cpiAccountCount`。

外层：payer s+w、seat PDA w、base vault w、quote vault w、mint r、Token。
本切片只开 seat PDA（种子 `"vault"`，跟 `createPda` 同一条）。
双 vault 的 `tokenInitAccount` 是下一切片：同一入口里两套 recipe
会把账户表拼在一起。
-/
namespace Examples.Seat

open ProofForge.Svm.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- 给 `"vault"` PDA 开 16 字节，当作席位账户。 -/
@[pf_entry]
def openSeat (_s : State) (lamports : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := createPda lamports
    .ok ({ dummy := 0 }, lamports)
  else
    .error .overflow

/-- 给 base vault 开 Token 账户。owner = acc0。 -/
@[pf_entry]
def openBase (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := tokenInitAccount
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  findPda "vault"

end Examples.Seat
