import ProofForge

/-!
Stamp the current ContractCall Sequence and Fee (drops) into JSON.
Host: tx_field(sfSequence=131076, sfFee=393224). Zero-arg for public RPC.
-/
namespace Examples.XrplTx

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  tseq : UInt64
  tfee : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init : State :=
  { tseq := 0, tfee := 0 }

@[pf_entry]
def stamp (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ tseq := Context.txSequence
           tfee := Context.txFeeDrops }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def getSeq (s : State) : UInt64 :=
  s.tseq

end Examples.XrplTx
