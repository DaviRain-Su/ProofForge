import Projects.PhoenixV1Profile
import ProofForge

namespace Tests.PhoenixV1ProfileSpec

open Projects.PhoenixV1Profile
open Lean Elab Command

#guard accountBytesFor 512 512 128 == 84944
#guard accountBytesFor 512 512 1025 == 214112
#guard accountBytesFor 512 512 1153 == 232544
#guard accountBytesFor 1024 1024 128 == 150480
#guard accountBytesFor 1024 1024 2049 == 427104
#guard accountBytesFor 1024 1024 2177 == 445536
#guard accountBytesFor 2048 2048 128 == 281552
#guard accountBytesFor 2048 2048 4097 == 853088
#guard accountBytesFor 2048 2048 4225 == 871520
#guard accountBytesFor 4096 4096 128 == 543696
#guard accountBytesFor 4096 4096 8193 == 1705056
#guard accountBytesFor 4096 4096 8321 == 1723488
#guard accountBytesFor 4 4 4 == 0
#guard accountBytesFor 512 1024 128 == 0
#guard boundedBodyEntryCount 512 128 1 2 3 == 6
#guard boundedBodyEntryCount 512 128 513 2 3 == 0
#guard boundedBodyEntryCount 512 128 1 2 129 == 0
#guard packUInt32 0x89abcdef 0x01234567 == 0x0123456789abcdef
#guard ProofForge.Svm.Runtime.svmByteSwap64 0x0706050403020100 == 0x0001020304050607
#guard key4Before 0x0100000000000000 0 0 0 0x00000000000000ff 0 0 0
#guard !key4Before 0x00000000000000ff 0 0 0 0x0100000000000000 0 0 0
#guard key4Before 7 0x0100000000000000 9 10 7 0x00000000000000ff 1 2
#guard !key4Before 7 0x00000000000000ff 1 2 7 0x0100000000000000 9 10
#guard key4Equal 1 2 3 4 1 2 3 4
#guard !key4Equal 1 2 3 4 1 2 3 5
#guard thirdRoot 1 == 2 && thirdNode1ParentColor 1 == 0x0000000100000002 &&
  thirdNode2Links 1 == 0x0000000100000003 && thirdNode3ParentColor 1 == 0x0000000100000002
#guard thirdRoot 2 == 3 && thirdNode1ParentColor 2 == 0x0000000100000003 &&
  thirdNode2ParentColor 2 == 0x0000000100000003 && thirdNode3Links 2 == 0x0000000100000002
#guard thirdRoot 3 == 1 && thirdNode1Links 3 == 0x0000000300000002 &&
  thirdNode2ParentColor 3 == 0x0000000100000001 &&
  thirdNode3ParentColor 3 == 0x0000000100000001
#guard thirdRoot 4 == 2 && thirdNode1ParentColor 4 == 0x0000000100000002 &&
  thirdNode2Links 4 == 0x0000000300000001 && thirdNode3ParentColor 4 == 0x0000000100000002
#guard thirdRoot 5 == 3 && thirdNode1ParentColor 5 == 0x0000000100000003 &&
  thirdNode2ParentColor 5 == 0x0000000100000003 && thirdNode3Links 5 == 0x0000000200000001
#guard thirdRoot 6 == 1 && thirdNode1Links 6 == 0x0000000200000003 &&
  thirdNode2ParentColor 6 == 0x0000000100000001 &&
  thirdNode3ParentColor 6 == 0x0000000100000001
#guard allocatorHeaderValid 512 0 0 0 ((1 : UInt64) ||| ((1 : UInt64) <<< (32 : UInt64)))
#guard allocatorHeaderValid 512 1 1 0 ((2 : UInt64) ||| ((2 : UInt64) <<< (32 : UInt64)))
#guard !allocatorHeaderValid 512 1 0 0 ((2 : UInt64) ||| ((2 : UInt64) <<< (32 : UInt64)))
#guard !allocatorHeaderValid 512 1 513 0
  ((514 : UInt64) ||| ((514 : UInt64) <<< (32 : UInt64)))
#guard !allocatorHeaderValid 512 1 1 0 ((1 : UInt64) ||| ((1 : UInt64) <<< (32 : UInt64)))
#guard !allocatorHeaderValid 512 1 1 0 ((2 : UInt64) ||| ((3 : UInt64) <<< (32 : UInt64)))
#guard nodeIndexOrNullValid 512 3 0
#guard nodeIndexOrNullValid 512 3 2
#guard !nodeIndexOrNullValid 512 3 3
#guard boundedBidRootPrice 512 3 0 0 999 == 999
#guard boundedBidRootPrice 512 3 3 0 999 == 0
#guard boundedBidRootPrice 512 3 0 ((1 : UInt64) <<< (32 : UInt64)) 999 == 0
#guard boundedNodeSlot 512 0 == 0
#guard boundedNodeSlot 512 2 == 1
#guard boundedNodeSlot 512 513 == 0
#guard bidKeyBefore 110 18446744073709551613 100 18446744073709551614
#guard !bidKeyBefore 90 18446744073709551613 100 18446744073709551614
#guard boundedBidChildValid 512 4 2 1 0
  (2 ||| ((1 : UInt64) <<< (32 : UInt64))) 18446744073709551613
#guard !boundedBidChildValid 512 4 2 1 0
  (2 ||| ((2 : UInt64) <<< (32 : UInt64))) 18446744073709551613

private partial def valHasDataWord (acc word : Nat) : ProofForge.Svm.Ops.Val → Bool
  | .ext (.accDataWord actualAcc actualWord) _ => actualAcc == acc && actualWord == word
  | .field base _ | .bitNot base => valHasDataWord acc word base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valHasDataWord acc word lhs || valHasDataWord acc word rhs
  | .indexGet base _ index _ _ =>
      valHasDataWord acc word base || valHasDataWord acc word index
  | .select _ lhs rhs thenValue elseValue =>
      valHasDataWord acc word lhs || valHasDataWord acc word rhs ||
        valHasDataWord acc word thenValue || valHasDataWord acc word elseValue
  | .ext _ operands => operands.any (valHasDataWord acc word)
  | _ => false

private partial def opsHaveDataWord (acc word : Nat) (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    let here :=
      match op with
      | .letLocal _ value | .setLocal _ value | .forAccum _ value _
      | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
          valHasDataWord acc word value
      | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
      | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
      | .indexSet _ lhs rhs _ _ =>
          valHasDataWord acc word lhs || valHasDataWord acc word rhs
      | .invoke _ _ data _ bump =>
          data.any (fun item => item.value?.any (valHasDataWord acc word)) ||
            bump.any (valHasDataWord acc word)
      | _ => false
    here ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveDataWord acc word thenOps || opsHaveDataWord acc word elseOps
      | .forBody _ body => opsHaveDataWord acc word body
      | _ => false

private partial def valHasIndexedDataWord
    (acc baseWord strideWords capacity : Nat) : ProofForge.Svm.Ops.Val → Bool
  | .ext (.accDataWordAt actualAcc actualBase actualStride actualCapacity) operands =>
      (actualAcc == acc && actualBase == baseWord && actualStride == strideWords &&
        actualCapacity == capacity) ||
        operands.any (valHasIndexedDataWord acc baseWord strideWords capacity)
  | .field base _ | .bitNot base => valHasIndexedDataWord acc baseWord strideWords capacity base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valHasIndexedDataWord acc baseWord strideWords capacity lhs ||
        valHasIndexedDataWord acc baseWord strideWords capacity rhs
  | .indexGet base _ index _ _ =>
      valHasIndexedDataWord acc baseWord strideWords capacity base ||
        valHasIndexedDataWord acc baseWord strideWords capacity index
  | .select _ lhs rhs thenValue elseValue =>
      valHasIndexedDataWord acc baseWord strideWords capacity lhs ||
        valHasIndexedDataWord acc baseWord strideWords capacity rhs ||
        valHasIndexedDataWord acc baseWord strideWords capacity thenValue ||
        valHasIndexedDataWord acc baseWord strideWords capacity elseValue
  | .ext _ operands => operands.any (valHasIndexedDataWord acc baseWord strideWords capacity)
  | _ => false

private partial def opsHaveIndexedDataWord
    (acc baseWord strideWords capacity : Nat) (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    let has := valHasIndexedDataWord acc baseWord strideWords capacity
    let here :=
      match op with
      | .letLocal _ value | .setLocal _ value | .forAccum _ value _
      | .storeField _ value | .okState value | .returnU64 value | .returnState value => has value
      | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
      | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
      | .indexSet _ lhs rhs _ _ => has lhs || has rhs
      | .invoke _ _ data _ bump =>
          data.any (fun item => item.value?.any has) || bump.any has
      | _ => false
    here ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveIndexedDataWord acc baseWord strideWords capacity thenOps ||
            opsHaveIndexedDataWord acc baseWord strideWords capacity elseOps
      | .forBody _ body => opsHaveIndexedDataWord acc baseWord strideWords capacity body
      | _ => false

private partial def valHasParentPath
    (acc linksBaseWord parentBaseWord strideWords capacity maxDepth : Nat) :
    ProofForge.Svm.Ops.Val → Bool
  | .ext (.accDataParentPathValid actualAcc actualLinks actualParent actualStride
      actualCapacity actualDepth) operands =>
      (actualAcc == acc && actualLinks == linksBaseWord && actualParent == parentBaseWord &&
        actualStride == strideWords && actualCapacity == capacity && actualDepth == maxDepth) ||
        operands.any (valHasParentPath
          acc linksBaseWord parentBaseWord strideWords capacity maxDepth)
  | .field base _ | .bitNot base =>
      valHasParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valHasParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth lhs ||
        valHasParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth rhs
  | .indexGet base _ index _ _ =>
      valHasParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth base ||
        valHasParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth index
  | .select _ lhs rhs thenValue elseValue =>
      valHasParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth lhs ||
        valHasParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth rhs ||
        valHasParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth thenValue ||
        valHasParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth elseValue
  | .ext _ operands => operands.any
      (valHasParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth)
  | _ => false

private partial def opsHaveParentPath
    (acc linksBaseWord parentBaseWord strideWords capacity maxDepth : Nat)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    let has := valHasParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth
    let here :=
      match op with
      | .letLocal _ value | .setLocal _ value | .forAccum _ value _
      | .storeField _ value | .okState value | .returnU64 value | .returnState value => has value
      | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
      | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
      | .indexSet _ lhs rhs _ _ => has lhs || has rhs
      | .invoke _ _ data _ bump =>
          data.any (fun item => item.value?.any has) || bump.any has
      | _ => false
    here ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth thenOps ||
            opsHaveParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth elseOps
      | .forBody _ body =>
          opsHaveParentPath acc linksBaseWord parentBaseWord strideWords capacity maxDepth body
      | _ => false

private partial def valHasRbTree
    (linksBase parentBase keyBase sequenceBase capacity : Nat) (expectedBid : Bool) :
    ProofForge.Svm.Ops.Val → Bool
  | .field base _ | .bitNot base =>
      valHasRbTree linksBase parentBase keyBase sequenceBase capacity expectedBid base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valHasRbTree linksBase parentBase keyBase sequenceBase capacity expectedBid lhs ||
        valHasRbTree linksBase parentBase keyBase sequenceBase capacity expectedBid rhs
  | .indexGet base _ index _ _ =>
      valHasRbTree linksBase parentBase keyBase sequenceBase capacity expectedBid base ||
        valHasRbTree linksBase parentBase keyBase sequenceBase capacity expectedBid index
  | .select _ lhs rhs thenValue elseValue =>
      valHasRbTree linksBase parentBase keyBase sequenceBase capacity expectedBid lhs ||
        valHasRbTree linksBase parentBase keyBase sequenceBase capacity expectedBid rhs ||
        valHasRbTree linksBase parentBase keyBase sequenceBase capacity expectedBid thenValue ||
        valHasRbTree linksBase parentBase keyBase sequenceBase capacity expectedBid elseValue
  | .ext (.accDataRbTreeValid actualAcc links parent key sequence stride actualCapacity bid)
      operands =>
      (actualAcc == 1 && links == linksBase && parent == parentBase && key == keyBase &&
        sequence == sequenceBase && stride == 8 && actualCapacity == capacity &&
        bid == expectedBid) ||
        operands.any
          (valHasRbTree linksBase parentBase keyBase sequenceBase capacity expectedBid)
  | .ext _ operands => operands.any
      (valHasRbTree linksBase parentBase keyBase sequenceBase capacity expectedBid)
  | _ => false

private partial def opsHaveRbTree
    (linksBase parentBase keyBase sequenceBase capacity : Nat) (bid : Bool)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    let has := valHasRbTree linksBase parentBase keyBase sequenceBase capacity bid
    let here :=
      match op with
      | .letLocal _ value | .setLocal _ value | .forAccum _ value _
      | .storeField _ value | .okState value | .returnU64 value | .returnState value => has value
      | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
      | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
      | .indexSet _ lhs rhs _ _ => has lhs || has rhs
      | .invoke _ _ data _ bump =>
          data.any (fun item => item.value?.any has) || bump.any has
      | _ => false
    here ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveRbTree linksBase parentBase keyBase sequenceBase capacity bid thenOps ||
            opsHaveRbTree linksBase parentBase keyBase sequenceBase capacity bid elseOps
      | .forBody _ body =>
          opsHaveRbTree linksBase parentBase keyBase sequenceBase capacity bid body
      | _ => false

private partial def valHasRbTreeKey4
    (linksBase parentBase keyBase capacity : Nat) : ProofForge.Svm.Ops.Val → Bool
  | .field base _ | .bitNot base =>
      valHasRbTreeKey4 linksBase parentBase keyBase capacity base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valHasRbTreeKey4 linksBase parentBase keyBase capacity lhs ||
        valHasRbTreeKey4 linksBase parentBase keyBase capacity rhs
  | .indexGet base _ index _ _ =>
      valHasRbTreeKey4 linksBase parentBase keyBase capacity base ||
        valHasRbTreeKey4 linksBase parentBase keyBase capacity index
  | .select _ lhs rhs thenValue elseValue =>
      valHasRbTreeKey4 linksBase parentBase keyBase capacity lhs ||
        valHasRbTreeKey4 linksBase parentBase keyBase capacity rhs ||
        valHasRbTreeKey4 linksBase parentBase keyBase capacity thenValue ||
        valHasRbTreeKey4 linksBase parentBase keyBase capacity elseValue
  | .ext (.accDataRbTreeKey4Valid actualAcc links parent key stride actualCapacity) operands =>
      (actualAcc == 1 && links == linksBase && parent == parentBase && key == keyBase &&
        stride == 18 && actualCapacity == capacity) ||
        operands.any (valHasRbTreeKey4 linksBase parentBase keyBase capacity)
  | .ext _ operands => operands.any
      (valHasRbTreeKey4 linksBase parentBase keyBase capacity)
  | _ => false

private partial def opsHaveRbTreeKey4
    (linksBase parentBase keyBase capacity : Nat)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    let has := valHasRbTreeKey4 linksBase parentBase keyBase capacity
    let here :=
      match op with
      | .letLocal _ value | .setLocal _ value | .forAccum _ value _
      | .storeField _ value | .okState value | .returnU64 value | .returnState value => has value
      | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
      | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
      | .indexSet _ lhs rhs _ _ => has lhs || has rhs
      | .invoke _ _ data _ bump =>
          data.any (fun item => item.value?.any has) || bump.any has
      | _ => false
    here ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveRbTreeKey4 linksBase parentBase keyBase capacity thenOps ||
            opsHaveRbTreeKey4 linksBase parentBase keyBase capacity elseOps
      | .forBody _ body => opsHaveRbTreeKey4 linksBase parentBase keyBase capacity body
      | _ => false

private partial def opsHaveDataWordSetAt
    (acc baseWord strideWords capacity : Nat)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .accDataWordSetAt actualAcc actualBase actualStride actualCapacity _ _ =>
         actualAcc == acc && actualBase == baseWord && actualStride == strideWords &&
           actualCapacity == capacity
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveDataWordSetAt acc baseWord strideWords capacity thenOps ||
            opsHaveDataWordSetAt acc baseWord strideWords capacity elseOps
      | .forBody _ body => opsHaveDataWordSetAt acc baseWord strideWords capacity body
      | _ => false

private partial def countDataWordSetAt (ops : Array ProofForge.Svm.IR.Op) : Nat :=
  ops.foldl (init := 0) fun count op =>
    count + match op with
    | .accDataWordSetAt .. => 1
    | .ite _ _ _ thenOps elseOps =>
        countDataWordSetAt thenOps + countDataWordSetAt elseOps
    | .forBody _ body => countDataWordSetAt body
    | _ => 0

private partial def opsHaveRbTreeKey4Insert
    (acc rootWord linksBase parentBase keyBase stride capacity : Nat)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .accDataRbTreeKey4Insert actualAcc actualRoot actualLinks actualParent actualKey
         actualStride actualCapacity _ _ _ _ =>
         actualAcc == acc && actualRoot == rootWord && actualLinks == linksBase &&
           actualParent == parentBase && actualKey == keyBase && actualStride == stride &&
           actualCapacity == capacity
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveRbTreeKey4Insert acc rootWord linksBase parentBase keyBase stride capacity
              thenOps ||
            opsHaveRbTreeKey4Insert acc rootWord linksBase parentBase keyBase stride capacity
              elseOps
      | .forBody _ body =>
          opsHaveRbTreeKey4Insert acc rootWord linksBase parentBase keyBase stride capacity body
      | _ => false

private partial def opsHaveRbTreeKey4Remove
    (acc rootWord linksBase parentBase keyBase stride capacity : Nat)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .accDataRbTreeKey4Remove actualAcc actualRoot actualLinks actualParent actualKey
         actualStride actualCapacity _ _ _ _ =>
         actualAcc == acc && actualRoot == rootWord && actualLinks == linksBase &&
           actualParent == parentBase && actualKey == keyBase && actualStride == stride &&
           actualCapacity == capacity
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveRbTreeKey4Remove acc rootWord linksBase parentBase keyBase stride capacity
              thenOps ||
            opsHaveRbTreeKey4Remove acc rootWord linksBase parentBase keyBase stride capacity
              elseOps
      | .forBody _ body =>
          opsHaveRbTreeKey4Remove acc rootWord linksBase parentBase keyBase stride capacity body
      | _ => false

private partial def opsHaveRbTreeTraderDeposit
    (acc rootWord linksBase parentBase keyBase stride capacity : Nat)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .accDataRbTreeTraderDeposit actualAcc actualRoot actualLinks actualParent actualKey
         actualStride actualCapacity _ _ _ _ _ _ =>
         actualAcc == acc && actualRoot == rootWord && actualLinks == linksBase &&
           actualParent == parentBase && actualKey == keyBase && actualStride == stride &&
           actualCapacity == capacity
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveRbTreeTraderDeposit acc rootWord linksBase parentBase keyBase stride capacity
              thenOps ||
            opsHaveRbTreeTraderDeposit acc rootWord linksBase parentBase keyBase stride capacity
              elseOps
      | .forBody _ body =>
          opsHaveRbTreeTraderDeposit acc rootWord linksBase parentBase keyBase stride capacity body
      | _ => false

private partial def opsHaveRbTreeOrderInsert
    (acc rootWord linksBase parentBase keyBase sequenceBase stride capacity : Nat) (bid : Bool)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .accDataRbTreeOrderInsert actualAcc actualRoot actualLinks actualParent actualKey
         actualSequence actualStride actualCapacity actualBid _ _ _ _ _ _ =>
         actualAcc == acc && actualRoot == rootWord && actualLinks == linksBase &&
           actualParent == parentBase && actualKey == keyBase && actualSequence == sequenceBase &&
           actualStride == stride && actualCapacity == capacity && actualBid == bid
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveRbTreeOrderInsert acc rootWord linksBase parentBase keyBase sequenceBase stride
              capacity bid thenOps ||
            opsHaveRbTreeOrderInsert acc rootWord linksBase parentBase keyBase sequenceBase stride
              capacity bid elseOps
      | .forBody _ body =>
          opsHaveRbTreeOrderInsert acc rootWord linksBase parentBase keyBase sequenceBase stride
            capacity bid body
      | _ => false

private partial def opsHaveRbTreeOrderRemove
    (acc rootWord linksBase parentBase keyBase sequenceBase stride capacity : Nat) (bid : Bool)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .accDataRbTreeOrderRemove actualAcc actualRoot actualLinks actualParent actualKey
         actualSequence actualStride actualCapacity actualBid _ _ =>
         actualAcc == acc && actualRoot == rootWord && actualLinks == linksBase &&
           actualParent == parentBase && actualKey == keyBase && actualSequence == sequenceBase &&
           actualStride == stride && actualCapacity == capacity && actualBid == bid
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveRbTreeOrderRemove acc rootWord linksBase parentBase keyBase sequenceBase stride
              capacity bid thenOps ||
            opsHaveRbTreeOrderRemove acc rootWord linksBase parentBase keyBase sequenceBase stride
              capacity bid elseOps
      | .forBody _ body =>
          opsHaveRbTreeOrderRemove acc rootWord linksBase parentBase keyBase sequenceBase stride
            capacity bid body
      | _ => false

elab "#pf_guard_phoenix_v1_profile" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Projects.PhoenixV1Profile none with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless ProofForge.Svm.IR.dataLen program == 16 &&
      ProofForge.Svm.IR.cpiAccountCount program == 2 do
    throwError "Phoenix-v1 profile verifier account layout changed"
  let some profile := program.methods.find? (·.ixName == "profileAccountBytes")
    | throwError "missing profileAccountBytes"
  let some seats := program.methods.find? (·.ixName == "headerSeats")
    | throwError "missing headerSeats"
  let some sequence := program.methods.find? (·.ixName == "marketSequence")
    | throwError "missing marketSequence"
  let some bodyCount := program.methods.find? (·.ixName == "bodyEntryCount")
    | throwError "missing bodyEntryCount"
  let some headersValid := program.methods.find? (·.ixName == "allocatorHeadersValid")
    | throwError "missing allocatorHeadersValid"
  let some rootPrice := program.methods.find? (·.ixName == "bidRootPrice")
    | throwError "missing bidRootPrice"
  let some neighborhood := program.methods.find? (·.ixName == "bidRootNeighborhoodValid")
    | throwError "missing bidRootNeighborhoodValid"
  let some parentPath := program.methods.find? (·.ixName == "bidParentPathValid")
    | throwError "missing bidParentPathValid"
  let some bidTree := program.methods.find? (·.ixName == "bidTreeValid")
    | throwError "missing bidTreeValid"
  let some askTree := program.methods.find? (·.ixName == "askTreeValid")
    | throwError "missing askTreeValid"
  let some traderTree := program.methods.find? (·.ixName == "traderTreeValid")
    | throwError "missing traderTreeValid"
  let some writeTrader := program.methods.find? (·.ixName == "writeTraderTopology128")
    | throwError "missing writeTraderTopology128"
  let some registerFirst := program.methods.find? (·.ixName == "registerFirstTrader128")
    | throwError "missing registerFirstTrader128"
  let some registerSecond := program.methods.find? (·.ixName == "registerSecondTrader128")
    | throwError "missing registerSecondTrader128"
  let some registerThird := program.methods.find? (·.ixName == "registerThirdTrader128")
    | throwError "missing registerThirdTrader128"
  let some registerFourth := program.methods.find? (·.ixName == "registerFourthTrader128")
    | throwError "missing registerFourthTrader128"
  let some registerFifth := program.methods.find? (·.ixName == "registerFifthTrader128")
    | throwError "missing registerFifthTrader128"
  let some registerGeneric := program.methods.find? (·.ixName == "registerTrader128")
    | throwError "missing registerTrader128"
  let some depositTrader := program.methods.find? (·.ixName == "depositTrader128")
    | throwError "missing depositTrader128"
  let some removeGeneric := program.methods.find? (·.ixName == "removeTrader128")
    | throwError "missing removeTrader128"
  let some insertBid := program.methods.find? (·.ixName == "insertBid512")
    | throwError "missing insertBid512"
  let some insertAsk := program.methods.find? (·.ixName == "insertAsk512")
    | throwError "missing insertAsk512"
  let some removeBid := program.methods.find? (·.ixName == "removeBid512")
    | throwError "missing removeBid512"
  let some removeAsk := program.methods.find? (·.ixName == "removeAsk512")
    | throwError "missing removeAsk512"
  unless opsHaveDataWord 1 0 profile.ops && opsHaveDataWord 1 2 profile.ops &&
      opsHaveDataWord 1 3 profile.ops && opsHaveDataWord 1 4 profile.ops &&
      opsHaveDataWord 1 4 seats.ops && opsHaveDataWord 1 106 sequence.ops &&
      opsHaveDataWord 1 112 bodyCount.ops && opsHaveDataWord 1 4212 bodyCount.ops &&
      opsHaveDataWord 1 8312 bodyCount.ops && opsHaveDataWord 1 8308 bodyCount.ops &&
      opsHaveDataWord 1 16504 bodyCount.ops && opsHaveDataWord 1 16500 bodyCount.ops &&
      opsHaveDataWord 1 32888 bodyCount.ops && opsHaveDataWord 1 32884 bodyCount.ops &&
      opsHaveDataWord 1 65656 bodyCount.ops && opsHaveDataWord 1 110 headersValid.ops &&
      opsHaveDataWord 1 113 headersValid.ops && opsHaveDataWord 1 4210 headersValid.ops &&
      opsHaveDataWord 1 4213 headersValid.ops && opsHaveDataWord 1 8310 headersValid.ops &&
      opsHaveDataWord 1 8313 headersValid.ops && opsHaveDataWord 1 8306 headersValid.ops &&
      opsHaveDataWord 1 8309 headersValid.ops && opsHaveDataWord 1 16502 headersValid.ops &&
      opsHaveDataWord 1 16505 headersValid.ops && opsHaveDataWord 1 16498 headersValid.ops &&
      opsHaveDataWord 1 16501 headersValid.ops && opsHaveDataWord 1 32886 headersValid.ops &&
      opsHaveDataWord 1 32889 headersValid.ops && opsHaveDataWord 1 32882 headersValid.ops &&
      opsHaveDataWord 1 32885 headersValid.ops && opsHaveDataWord 1 65654 headersValid.ops &&
      opsHaveDataWord 1 65657 headersValid.ops &&
      opsHaveIndexedDataWord 1 114 8 512 rootPrice.ops &&
      opsHaveIndexedDataWord 1 115 8 1024 rootPrice.ops &&
      opsHaveIndexedDataWord 1 116 8 2048 rootPrice.ops &&
      opsHaveIndexedDataWord 1 116 8 4096 rootPrice.ops &&
      opsHaveIndexedDataWord 1 117 8 512 neighborhood.ops &&
      opsHaveIndexedDataWord 1 117 8 1024 neighborhood.ops &&
      opsHaveIndexedDataWord 1 117 8 2048 neighborhood.ops &&
      opsHaveIndexedDataWord 1 117 8 4096 neighborhood.ops &&
      opsHaveParentPath 1 114 115 8 512 32 parentPath.ops &&
      opsHaveParentPath 1 114 115 8 1024 32 parentPath.ops &&
      opsHaveParentPath 1 114 115 8 2048 32 parentPath.ops &&
      opsHaveParentPath 1 114 115 8 4096 32 parentPath.ops &&
      opsHaveRbTree 114 115 116 117 512 true bidTree.ops &&
      opsHaveRbTree 114 115 116 117 1024 true bidTree.ops &&
      opsHaveRbTree 114 115 116 117 2048 true bidTree.ops &&
      opsHaveRbTree 114 115 116 117 4096 true bidTree.ops &&
      opsHaveRbTree 4214 4215 4216 4217 512 false askTree.ops &&
      opsHaveRbTree 8310 8311 8312 8313 1024 false askTree.ops &&
      opsHaveRbTree 16502 16503 16504 16505 2048 false askTree.ops &&
      opsHaveRbTree 32886 32887 32888 32889 4096 false askTree.ops &&
      opsHaveRbTreeKey4 8314 8315 8316 128 traderTree.ops &&
      opsHaveRbTreeKey4 8314 8315 8316 1025 traderTree.ops &&
      opsHaveRbTreeKey4 8314 8315 8316 1153 traderTree.ops &&
      opsHaveRbTreeKey4 16506 16507 16508 128 traderTree.ops &&
      opsHaveRbTreeKey4 16506 16507 16508 2049 traderTree.ops &&
      opsHaveRbTreeKey4 16506 16507 16508 2177 traderTree.ops &&
      opsHaveRbTreeKey4 32890 32891 32892 128 traderTree.ops &&
      opsHaveRbTreeKey4 32890 32891 32892 4097 traderTree.ops &&
      opsHaveRbTreeKey4 32890 32891 32892 4225 traderTree.ops &&
      opsHaveRbTreeKey4 65658 65659 65660 128 traderTree.ops &&
      opsHaveRbTreeKey4 65658 65659 65660 8193 traderTree.ops &&
      opsHaveRbTreeKey4 65658 65659 65660 8321 traderTree.ops &&
      opsHaveDataWordSetAt 1 8314 18 128 writeTrader.ops &&
      opsHaveDataWordSetAt 1 8315 18 128 writeTrader.ops &&
      opsHaveDataWord 1 8310 registerFirst.ops &&
      opsHaveDataWord 1 8313 registerFirst.ops &&
      opsHaveDataWordSetAt 1 8310 1 1 registerFirst.ops &&
      opsHaveDataWordSetAt 1 8312 1 1 registerFirst.ops &&
      opsHaveDataWordSetAt 1 8313 1 1 registerFirst.ops &&
      (List.range 18).all (fun offset =>
        opsHaveDataWordSetAt 1 (8314 + offset) 18 128 registerFirst.ops) &&
      countDataWordSetAt registerFirst.ops == 21 &&
      opsHaveDataWord 1 8314 registerSecond.ops &&
      opsHaveDataWord 1 8315 registerSecond.ops &&
      opsHaveDataWord 1 8316 registerSecond.ops &&
      opsHaveDataWord 1 8319 registerSecond.ops &&
      opsHaveDataWordSetAt 1 8312 1 1 registerSecond.ops &&
      opsHaveDataWordSetAt 1 8313 1 1 registerSecond.ops &&
      (List.range 18).all (fun offset =>
        opsHaveDataWordSetAt 1 (8314 + offset) 18 128 registerSecond.ops) &&
      countDataWordSetAt registerSecond.ops == 21 &&
      opsHaveDataWord 1 8314 registerThird.ops &&
      opsHaveDataWord 1 8319 registerThird.ops &&
      opsHaveDataWord 1 8332 registerThird.ops &&
      opsHaveDataWord 1 8333 registerThird.ops &&
      opsHaveDataWord 1 8334 registerThird.ops &&
      opsHaveDataWord 1 8337 registerThird.ops &&
      opsHaveDataWordSetAt 1 8310 1 1 registerThird.ops &&
      opsHaveDataWordSetAt 1 8312 1 1 registerThird.ops &&
      opsHaveDataWordSetAt 1 8313 1 1 registerThird.ops &&
      (List.range 18).all (fun offset =>
        opsHaveDataWordSetAt 1 (8314 + offset) 18 128 registerThird.ops) &&
      countDataWordSetAt registerThird.ops == 25 &&
      opsHaveIndexedDataWord 1 8314 18 128 registerFourth.ops &&
      opsHaveIndexedDataWord 1 8316 18 128 registerFourth.ops &&
      opsHaveIndexedDataWord 1 8317 18 128 registerFourth.ops &&
      opsHaveIndexedDataWord 1 8318 18 128 registerFourth.ops &&
      opsHaveIndexedDataWord 1 8319 18 128 registerFourth.ops &&
      opsHaveRbTreeKey4 8314 8315 8316 128 registerFourth.ops &&
      opsHaveDataWordSetAt 1 8312 1 1 registerFourth.ops &&
      opsHaveDataWordSetAt 1 8313 1 1 registerFourth.ops &&
      (List.range 18).all (fun offset =>
        opsHaveDataWordSetAt 1 (8314 + offset) 18 128 registerFourth.ops) &&
      countDataWordSetAt registerFourth.ops == 23 &&
      opsHaveIndexedDataWord 1 8314 18 128 registerFifth.ops &&
      opsHaveIndexedDataWord 1 8315 18 128 registerFifth.ops &&
      opsHaveIndexedDataWord 1 8316 18 128 registerFifth.ops &&
      opsHaveIndexedDataWord 1 8317 18 128 registerFifth.ops &&
      opsHaveIndexedDataWord 1 8318 18 128 registerFifth.ops &&
      opsHaveIndexedDataWord 1 8319 18 128 registerFifth.ops &&
      opsHaveRbTreeKey4 8314 8315 8316 128 registerFifth.ops &&
      opsHaveDataWordSetAt 1 8312 1 1 registerFifth.ops &&
      opsHaveDataWordSetAt 1 8313 1 1 registerFifth.ops &&
      (List.range 18).all (fun offset =>
        opsHaveDataWordSetAt 1 (8314 + offset) 18 128 registerFifth.ops) &&
      countDataWordSetAt registerFifth.ops == 27 &&
      opsHaveDataWord 1 8311 registerGeneric.ops &&
      opsHaveRbTreeKey4Insert 1 8310 8314 8315 8316 18 128 registerGeneric.ops &&
      countDataWordSetAt registerGeneric.ops == 0 &&
      opsHaveDataWord 1 8311 depositTrader.ops &&
      opsHaveRbTreeTraderDeposit 1 8310 8314 8315 8316 18 128 depositTrader.ops &&
      countDataWordSetAt depositTrader.ops == 0 &&
      opsHaveDataWord 1 8311 removeGeneric.ops &&
      opsHaveRbTreeKey4Remove 1 8310 8314 8315 8316 18 128 removeGeneric.ops &&
      countDataWordSetAt removeGeneric.ops == 0 &&
      opsHaveDataWord 1 111 insertBid.ops &&
      opsHaveRbTreeOrderInsert 1 110 114 115 116 117 8 512 true insertBid.ops &&
      countDataWordSetAt insertBid.ops == 0 &&
      opsHaveDataWord 1 4211 insertAsk.ops &&
      opsHaveRbTreeOrderInsert 1 4210 4214 4215 4216 4217 8 512 false insertAsk.ops &&
      countDataWordSetAt insertAsk.ops == 0 &&
      opsHaveDataWord 1 111 removeBid.ops &&
      opsHaveRbTreeOrderRemove 1 110 114 115 116 117 8 512 true removeBid.ops &&
      countDataWordSetAt removeBid.ops == 0 &&
      opsHaveDataWord 1 4211 removeAsk.ops &&
      opsHaveRbTreeOrderRemove 1 4210 4214 4215 4216 4217 8 512 false removeAsk.ops &&
      countDataWordSetAt removeAsk.ops == 0 do
    throwError "Phoenix-v1 profile/body header reads are incomplete"
  let idl := ProofForge.Svm.Idl.emitProgramIdl program
  unless idl.contains
      "\"name\": \"registerTrader128\",\n      \"discriminator\": [90, 37, 2, 213, 222, 9, 17, 252],\n      \"accounts\": [{\"name\":\"state\",\"writable\":true,\"signer\":true}, {\"name\":\"acc1\",\"writable\":true}]" do
    throwError "registerTrader128 IDL account must be writable"
  unless idl.contains
      "\"name\": \"depositTrader128\",\n      \"discriminator\": [135, 20, 238, 244, 5, 95, 239, 55],\n      \"accounts\": [{\"name\":\"state\",\"writable\":true,\"signer\":true}, {\"name\":\"acc1\",\"writable\":true}]" do
    throwError "depositTrader128 IDL account must be writable"
  unless idl.contains
      "\"name\": \"removeTrader128\",\n      \"discriminator\": [250, 180, 99, 67, 51, 160, 35, 171],\n      \"accounts\": [{\"name\":\"state\",\"writable\":true,\"signer\":true}, {\"name\":\"acc1\",\"writable\":true}]" do
    throwError "removeTrader128 IDL account must be writable"
  unless idl.contains
      "\"name\": \"insertBid512\",\n      \"discriminator\": [251, 133, 14, 255, 81, 210, 196, 146],\n      \"accounts\": [{\"name\":\"state\",\"writable\":true,\"signer\":true}, {\"name\":\"acc1\",\"writable\":true}]" do
    throwError "insertBid512 IDL account must be writable"
  unless idl.contains
      "\"name\": \"insertAsk512\",\n      \"discriminator\": [243, 131, 134, 138, 16, 250, 118, 146],\n      \"accounts\": [{\"name\":\"state\",\"writable\":true,\"signer\":true}, {\"name\":\"acc1\",\"writable\":true}]" do
    throwError "insertAsk512 IDL account must be writable"
  unless idl.contains
      "\"name\": \"removeBid512\",\n      \"discriminator\": [137, 32, 120, 253, 28, 196, 175, 219],\n      \"accounts\": [{\"name\":\"state\",\"writable\":true,\"signer\":true}, {\"name\":\"acc1\",\"writable\":true}]" do
    throwError "removeBid512 IDL account must be writable"
  unless idl.contains
      "\"name\": \"removeAsk512\",\n      \"discriminator\": [213, 48, 137, 162, 87, 173, 116, 53],\n      \"accounts\": [{\"name\":\"state\",\"writable\":true,\"signer\":true}, {\"name\":\"acc1\",\"writable\":true}]" do
    throwError "removeAsk512 IDL account must be writable"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "load walked acc1 data word 4" &&
      asm.contains "ldxdw r2, [r1 + 80]" &&
      asm.contains "jge r2, r3, ok_data_word_" &&
      asm.contains "add64 r1, 88" && asm.contains "jlt r1, 2" &&
      asm.contains "load bounded acc1 data word base=116 stride=8 capacity=4096" &&
      asm.contains "mul64 r2, r3" &&
      asm.contains "validate bounded acc1 parent path links=114 parent=115 stride=8 capacity=4096 depth=32" &&
      asm.contains "parent_path_loop_" &&
      asm.contains "complete account-resident RB tree and allocator validation" &&
      asm.contains "stride=8 capacity=4096 bid=true" &&
      asm.contains "stride=8 capacity=4096 bid=false" && asm.contains "rb_free_loop_" &&
      asm.contains "complete four-word-key account-resident RB tree" &&
      asm.contains "key4=65660 stride=18 capacity=8321" && asm.contains "be64 r1" &&
      asm.contains "r7 remains the walked instruction-data base outside this intrinsic" &&
      asm.contains "rb4_free_loop_" && asm.contains "add64 r9, -4096" &&
      asm.contains "add64 r9, -3000" &&
      asm.contains "fixed-stride external account word write acc=1 base=8314 stride=18 capacity=128" &&
      asm.contains "fixed-stride external account word write acc=1 base=8315 stride=18 capacity=128" &&
      asm.contains "fixed-stride external account word write acc=1 base=8331 stride=18 capacity=128" &&
      asm.contains "fixed-stride external account word write acc=1 base=8310 stride=1 capacity=1" &&
      asm.contains "ownerIsSelf acc=1" && asm.contains "dws_failure_" &&
      asm.contains "bounded account-resident four-word-key RB insertion" &&
      asm.contains "root=8310 links=8314 parent=8315 key4=8316 stride=18 capacity=128" &&
      asm.contains "function_rb4i_" && asm.contains "_rotate_left" &&
      asm.contains "_rotate_right" &&
      asm.contains "bounded account-resident Phoenix trader deposit RB insertion" &&
      asm.contains "function_rbtd_" &&
      asm.contains "Existing trader: validate both additions before mutating either free balance" &&
      asm.contains "ldxdw r1, [r8 + 40]" && asm.contains "ldxdw r1, [r8 + 56]" &&
      asm.contains "jlt r3, r1, rbtd_" && asm.contains "stxdw [r10 - 56], r3" &&
      asm.contains "stxdw [r10 - 64], r3" &&
      asm.contains "bounded account-resident four-word-key RB removal" &&
      asm.contains "function_rb4r_" && asm.contains "_transplant" &&
      asm.contains "bounded account-resident Phoenix bid order RB insertion" &&
      asm.contains "root=110 links=114 parent=115 key=116 stride=8 capacity=512" &&
      asm.contains "bounded account-resident Phoenix ask order RB insertion" &&
      asm.contains "root=4210 links=4214 parent=4215 key=4216 stride=8 capacity=512" &&
      asm.contains "Sokoban map semantics replace only the existing resting-order value" &&
      asm.contains "stxdw [r8 + 16], r1" && asm.contains "stxdw [r8 + 40], r1" &&
      asm.contains "rsh64 r1, 63" && asm.contains "jne r1, 1" && asm.contains "jne r1, 0" &&
      asm.contains "function_rboi_" &&
      asm.contains "bounded account-resident Phoenix bid order RB removal" &&
      asm.contains "bounded account-resident Phoenix ask order RB removal" &&
      asm.contains "function_rbor_" && asm.contains "_transplant" do
    throwError "Phoenix-v1 account data bounds gate is missing"

#pf_guard_phoenix_v1_profile

end Tests.PhoenixV1ProfileSpec
