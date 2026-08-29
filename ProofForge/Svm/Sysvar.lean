import ProofForge.Svm.AccountStorage

/-!
# SVM sysvar queries

Target-owned query vocabulary for Solana sysvars that are copied into fixed stack scratch by the
official host functions. Queries carry no account effect, allocation, source-visible pointer, or
persistent state; generic SVM Ops/IR/CFG use only the existing Component bridge.
-/

namespace ProofForge.Svm.Sysvar

inductive ClockField where
  | slot
  | epoch
  | leaderScheduleEpoch
  | unixTimestamp
  deriving BEq, Repr, Inhabited

inductive EpochScheduleField where
  | slotsPerEpoch
  | leaderScheduleSlotOffset
  | warmup
  | firstNormalEpoch
  | firstNormalSlot
  deriving BEq, Repr, Inhabited

inductive Query where
  | clock (field : ClockField)
  | epochSchedule (field : EpochScheduleField)
  | rentExemption (dataLen : UInt64)
  deriving BEq, Repr, Inhabited

def Query.arity (_query : Query) : Nat := 0

def Query.effects (_query : Query) : AccountStorage.EffectSummary := {}

def Query.wellFormed (_query : Query) : Bool := true

def Query.needsWalk (_query : Query) : Bool := false

def Query.minAccounts (measure : V → Nat) (operands : Array V) (_query : Query) : Nat :=
  operands.foldl (init := 0) fun current value => Nat.max current (measure value)

private def Query.name : Query → String
  | .clock .slot => "clk"
  | .clock .epoch => "epo"
  | .clock .leaderScheduleEpoch => "clock.leaderScheduleEpoch"
  | .clock .unixTimestamp => "unix"
  | .epochSchedule .slotsPerEpoch => "spe"
  | .epochSchedule .leaderScheduleSlotOffset => "epochSchedule.leaderScheduleSlotOffset"
  | .epochSchedule .warmup => "epochSchedule.warmup"
  | .epochSchedule .firstNormalEpoch => "epochSchedule.firstNormalEpoch"
  | .epochSchedule .firstNormalSlot => "epochSchedule.firstNormalSlot"
  | .rentExemption dataLen => s!"rent.{dataLen.toNat}"

def Query.canonical (renderValue : V → String) (operands : Array V) (query : Query) : String :=
  if operands.isEmpty then query.name
  else s!"invalid-{query.name}-{operands.size}-" ++
    String.intercalate "," (operands.map renderValue).toList

end ProofForge.Svm.Sysvar
