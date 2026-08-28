import ProofForge

/-!
席位 PDA + vault 初始化。不跟 Phoenix 挂单/吃单混：
CPI 账户表不同，混在一个 Program 会抬高 `cpiAccountCount`。

`openSeat` 的外层账户是 payer s+w、seat PDA w、System；`openBase` / `openQuote`
分别把一组 owner、vault、mint、Token 绑定到同一条 `Sdk.Token.initializeAccount` recipe。
双 vault 同一入口会需要两组不同的账户索引，留给 Phoenix adapter 切片。
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
    let _ := ProofForge.Svm.Sdk.Token.initializeAccount
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

/-- 给 quote vault 开 Token 账户。owner = acc0。 -/
@[pf_entry]
def openQuote (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := ProofForge.Svm.Sdk.Token.initializeAccount
    .ok ({ dummy := 0 }, 0)
  else
    .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 :=
  findPda "vault"

end Examples.Seat
