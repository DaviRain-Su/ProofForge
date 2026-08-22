import SolanaLean

namespace Examples.CreatePda

open SolanaLean.Runtime

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[solana_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

/-- 给 `"vault"` PDA 开 16 字节。 -/
@[solana_entry]
def openPda (_s : State) (lamports : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := createPda lamports
    .ok ({ dummy := 0 }, lamports)
  else
    .error .overflow

/-- 同一条 CreateAccount，bump 钉死 0。syscall 必须失败。 -/
@[solana_entry]
def openBad (_s : State) (lamports : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    let _ := invokeSigned 2
      #[{ acc := 0, signer := true, writable := true },
        { acc := 1, signer := true, writable := true }]
      #[.u32le 0, .u64le lamports, .u64le 16, .programId]
      "vault" 0
    .ok ({ dummy := 0 }, lamports)
  else
    .error .overflow

@[solana_entry]
def get (_s : State) : UInt64 :=
  0

end Examples.CreatePda
