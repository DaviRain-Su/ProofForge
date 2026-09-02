import Examples.PhoenixV1Profile
import ProofForge

namespace Tests.PhoenixV1ProfileSpec

open Examples.PhoenixV1Profile
open Lean Elab Command

set_option maxRecDepth 2048

#guard (Examples.PhoenixV1.small 2).wellFormed
#guard (Examples.PhoenixV1.small 2).accountBytes == 84944
#guard (Examples.PhoenixV1.small 2).bids.map ==
  ProofForge.Svm.AccountStorage.RbMap.fifoOneBased 2 110 114 115 116 117 8 512 true
#guard (Examples.PhoenixV1.small 2).asks.map ==
  ProofForge.Svm.AccountStorage.RbMap.fifoOneBased 2 4210 4214 4215 4216 4217 8 512 false
#guard (Examples.PhoenixV1.small 2).traders.map ==
  ProofForge.Svm.AccountStorage.RbMap.key4OneBased 2 8310 8314 8315 8316 18 128
#guard (Examples.PhoenixV1.small 2).bids.wellFormed
#guard (Examples.PhoenixV1.small 2).asks.wellFormed
#guard (Examples.PhoenixV1.small 2).bids.map.allocator.wellFormed
#guard (Examples.PhoenixV1.small 2).bids.map.allocator.liveCount.firstWord == 112
#guard (Examples.PhoenixV1.small 2).bids.map.allocator.cursor.firstWord == 113

private def malformedPhoenixBook : Examples.PhoenixV1.Book :=
  let book := (Examples.PhoenixV1.small 2).bids
  { book with owner := ProofForge.Svm.AccountStorage.Field.scalar 2 118 }

#guard !malformedPhoenixBook.wellFormed

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
  | .ext (.component (.accountStorage (.readWord field))) operands =>
      (field.region.account == acc && field.firstWord == word &&
        field.region.strideWords == 1 && field.region.capacity == 1) ||
        operands.any (valHasDataWord acc word)
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
  | .ext (.component (.accountStorage (.readWord field))) operands =>
      (field.region.account == acc && field.firstWord == baseWord &&
        field.region.strideWords == strideWords && field.region.capacity == capacity &&
        field.region.indexBase == .zero) ||
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
      | .component call => call.values.any has
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
  | .ext (.component (.accountStorage (.parentPathValid path))) operands =>
      (path.links.region.account == acc && path.links.firstWord == linksBaseWord &&
        path.parentColor.firstWord == parentBaseWord &&
        path.links.region.strideWords == strideWords &&
        path.links.region.capacity == capacity && path.maxDepth == maxDepth) ||
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
      | .component call => call.values.any has
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
  | .ext (.component (.accountStorage (.fifoRbTreeValid tree))) operands =>
      let region := tree.links.region
      (region.account == 1 && tree.links.firstWord == linksBase &&
        tree.parentColor.firstWord == parentBase && tree.price.firstWord == keyBase &&
        tree.sequence.firstWord == sequenceBase && region.strideWords == 8 &&
        region.capacity == capacity && tree.bid == expectedBid) ||
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
  | .ext (.component (.accountStorage (.key4RbTreeValid tree))) operands =>
      let region := tree.links.region
      (region.account == 1 && tree.links.firstWord == linksBase &&
        tree.parentColor.firstWord == parentBase && tree.key.firstWord == keyBase &&
        region.strideWords == 18 && region.capacity == capacity) ||
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
     | .component (.accountStorage (.writeWord field _ _)) =>
         field.region.account == acc && field.firstWord == baseWord &&
           field.region.strideWords == strideWords && field.region.capacity == capacity
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveDataWordSetAt acc baseWord strideWords capacity thenOps ||
            opsHaveDataWordSetAt acc baseWord strideWords capacity elseOps
      | .forBody _ body => opsHaveDataWordSetAt acc baseWord strideWords capacity body
      | _ => false

private partial def opsHaveOneBasedDataWordSetAt
    (acc baseWord strideWords capacity : Nat)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .component (.accountStorage (.writeWord field _ _)) =>
         field.region.account == acc && field.firstWord == baseWord &&
           field.region.strideWords == strideWords && field.region.capacity == capacity &&
           field.region.indexBase == .one
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveOneBasedDataWordSetAt acc baseWord strideWords capacity thenOps ||
            opsHaveOneBasedDataWordSetAt acc baseWord strideWords capacity elseOps
      | .forBody _ body =>
          opsHaveOneBasedDataWordSetAt acc baseWord strideWords capacity body
      | _ => false

private partial def countDataWordSetAt (ops : Array ProofForge.Svm.IR.Op) : Nat :=
  ops.foldl (init := 0) fun count op =>
    count + match op with
    | .component (.accountStorage (.writeWord ..)) => 1
    | .ite _ _ _ thenOps elseOps =>
        countDataWordSetAt thenOps + countDataWordSetAt elseOps
    | .forBody _ body => countDataWordSetAt body
    | _ => 0

private partial def opsHaveRbTreeKey4Insert
    (acc rootWord linksBase parentBase keyBase stride capacity : Nat)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .component (.accountStorage
         (.rbMapInsert (.key4 actualRoot tree) _ _ .reject)) =>
         tree.links.region.account == acc && actualRoot == rootWord &&
           tree.links.firstWord == linksBase && tree.parentColor.firstWord == parentBase &&
           tree.key.firstWord == keyBase && tree.links.region.strideWords == stride &&
           tree.links.region.capacity == capacity
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
     | .component (.accountStorage (.rbMapRemove (.key4 actualRoot tree) _)) =>
         tree.links.region.account == acc && actualRoot == rootWord &&
           tree.links.firstWord == linksBase && tree.parentColor.firstWord == parentBase &&
           tree.key.firstWord == keyBase && tree.links.region.strideWords == stride &&
           tree.links.region.capacity == capacity
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
     | .component (.accountStorage (.rbMapCheckedAdd (.key4 actualRoot tree) _ _)) =>
         tree.links.region.account == acc && actualRoot == rootWord &&
           tree.links.firstWord == linksBase && tree.parentColor.firstWord == parentBase &&
           tree.key.firstWord == keyBase && tree.links.region.strideWords == stride &&
           tree.links.region.capacity == capacity
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
     | .component (.accountStorage
         (.rbMapInsert (.fifo actualRoot tree) _ _ .replace)) =>
         tree.links.region.account == acc && actualRoot == rootWord &&
           tree.links.firstWord == linksBase && tree.parentColor.firstWord == parentBase &&
           tree.price.firstWord == keyBase && tree.sequence.firstWord == sequenceBase &&
           tree.links.region.strideWords == stride && tree.links.region.capacity == capacity &&
           tree.bid == bid
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
     | .component (.accountStorage (.rbMapRemove (.fifo actualRoot tree) _)) =>
         tree.links.region.account == acc && actualRoot == rootWord &&
           tree.links.firstWord == linksBase && tree.parentColor.firstWord == parentBase &&
           tree.price.firstWord == keyBase && tree.sequence.firstWord == sequenceBase &&
           tree.links.region.strideWords == stride && tree.links.region.capacity == capacity &&
           tree.bid == bid
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

private partial def valHasAccountQuery
    (predicate : ProofForge.Svm.AccountStorage.Query → Bool) :
    ProofForge.Svm.Ops.Val → Bool
  | .ext (.component (.accountStorage query)) operands =>
      predicate query || operands.any (valHasAccountQuery predicate)
  | .field base _ | .bitNot base => valHasAccountQuery predicate base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valHasAccountQuery predicate lhs || valHasAccountQuery predicate rhs
  | .indexGet base _ index _ _ =>
      valHasAccountQuery predicate base || valHasAccountQuery predicate index
  | .select _ lhs rhs thenValue elseValue =>
      valHasAccountQuery predicate lhs || valHasAccountQuery predicate rhs ||
        valHasAccountQuery predicate thenValue || valHasAccountQuery predicate elseValue
  | .ext _ operands => operands.any (valHasAccountQuery predicate)
  | _ => false

private partial def opsHaveAccountQuery
    (predicate : ProofForge.Svm.AccountStorage.Query → Bool)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    let has := valHasAccountQuery predicate
    let here :=
      match op with
      | .letLocal _ value | .setLocal _ value | .forAccum _ value _
      | .storeField _ value | .okState value | .returnU64 value | .returnState value => has value
      | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
      | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
      | .indexSet _ lhs rhs _ _ => has lhs || has rhs
      | .invoke _ _ data _ bump =>
          data.any (fun item => item.value?.any has) || bump.any has
      | .component call => call.values.any has
      | _ => false
    here ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveAccountQuery predicate thenOps || opsHaveAccountQuery predicate elseOps
      | .forBody _ body => opsHaveAccountQuery predicate body
      | _ => false

private partial def valHasIntrinsic
    (predicate : ProofForge.Svm.Ops.ValKind → Bool) : ProofForge.Svm.Ops.Val → Bool
  | .field base _ | .bitNot base => valHasIntrinsic predicate base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valHasIntrinsic predicate lhs || valHasIntrinsic predicate rhs
  | .indexGet base _ index _ _ =>
      valHasIntrinsic predicate base || valHasIntrinsic predicate index
  | .select _ lhs rhs thenValue elseValue =>
      valHasIntrinsic predicate lhs || valHasIntrinsic predicate rhs ||
        valHasIntrinsic predicate thenValue || valHasIntrinsic predicate elseValue
  | .ext kind operands => predicate kind || operands.any (valHasIntrinsic predicate)
  | _ => false

private partial def opsHaveIntrinsic
    (predicate : ProofForge.Svm.Ops.ValKind → Bool)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    let has := valHasIntrinsic predicate
    let here :=
      match op with
      | .letLocal _ value | .setLocal _ value | .forAccum _ value _
      | .storeField _ value | .okState value | .returnU64 value | .returnState value => has value
      | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
      | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
      | .indexSet _ lhs rhs _ _ => has lhs || has rhs
      | .invoke _ _ data _ bump =>
          data.any (fun item => item.value?.any has) || bump.any has
      | .component call => call.values.any has
      | _ => false
    here ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveIntrinsic predicate thenOps || opsHaveIntrinsic predicate elseOps
      | .forBody _ body => opsHaveIntrinsic predicate body
      | _ => false

private def isPhoenixRecorderConfig (config : ProofForge.Svm.BatchRecorder.Config) : Bool :=
  config == {
    logAccount := 0
    selfEntryTag := 15
    authoritySeed := "log"
    maxBytes := 1246
    headerBytes := 93
    countOffset := 91
    maxRecords := 32
  }

private partial def opsHaveRawReduceRecord
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .component (.batchRecorder (.append config _ record)) =>
         isPhoenixRecorderConfig config && record.size == 6 &&
           record[0]? == some (.u8le (.lit 4)) &&
           (match record[1]? with
            | some (ProofForge.Svm.BatchRecorder.Word.u16le _) => true | _ => false) &&
           (match record[2]? with
            | some (ProofForge.Svm.BatchRecorder.Word.u64le _) => true | _ => false) &&
           (match record[3]? with
            | some (ProofForge.Svm.BatchRecorder.Word.u64le _) => true | _ => false) &&
           (match record[4]? with
            | some (ProofForge.Svm.BatchRecorder.Word.u64le _) => true | _ => false) &&
           (match record[5]? with
            | some (ProofForge.Svm.BatchRecorder.Word.u64le _) => true | _ => false)
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveRawReduceRecord thenOps || opsHaveRawReduceRecord elseOps
      | .forBody _ body => opsHaveRawReduceRecord body
      | _ => false

private partial def opsHaveRawPlaceRecord
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .component (.batchRecorder (.append config enabled record)) =>
         isPhoenixRecorderConfig config && enabled == .lit 1 && record.size == 7 &&
           record[0]? == some (.u8le (.lit 3)) &&
           (match record[1]? with
            | some (ProofForge.Svm.BatchRecorder.Word.u16le _) => true | _ => false) &&
           (List.range 5).all fun index =>
             match record[index + 2]? with
             | some (ProofForge.Svm.BatchRecorder.Word.u64le _) => true
             | _ => false
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveRawPlaceRecord thenOps || opsHaveRawPlaceRecord elseOps
      | .forBody _ body => opsHaveRawPlaceRecord body
      | _ => false

private partial def opsHaveRawReduceHeader (origin : UInt64)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .component (.batchRecorder (.begin config header bump)) =>
         isPhoenixRecorderConfig config && bump == .ext (.findPda "log") #[] &&
           header.size == 11 && header[0]? == some (.u8le (.lit 1)) &&
           header[1]? == some (.u8le (.lit origin)) &&
           header[3]? == some (.u64le
             (.ext (.component (.sysvar (.clock .unixTimestamp))) #[])) &&
           header[4]? == some (.u64le
             (.ext (.component (.sysvar (.clock .slot))) #[])) &&
           header[5]? == some (.u64le (.ext (.accKeyWord 2 0) #[])) &&
           header[6]? == some (.u64le (.ext (.accKeyWord 2 1) #[])) &&
           header[7]? == some (.u64le (.ext (.accKeyWord 2 2) #[])) &&
           header[8]? == some (.u64le (.ext (.accKeyWord 2 3) #[])) &&
           header[9]? == some (.accountKey 2) && header[10]? == some (.u16le (.lit 0))
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveRawReduceHeader origin thenOps || opsHaveRawReduceHeader origin elseOps
      | .forBody _ body => opsHaveRawReduceHeader origin body
      | _ => false

private partial def opsHaveRawReduceFinish (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .component (.batchRecorder (.finish config)) => isPhoenixRecorderConfig config
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveRawReduceFinish thenOps || opsHaveRawReduceFinish elseOps
      | .forBody _ body => opsHaveRawReduceFinish body
      | _ => false

private partial def opsHaveUncheckedTransfer
    (source destination authority : Nat) (seeds : Array ProofForge.Svm.Ops.PdaSeed)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .invoke programIx metas data actualSeeds (some _) =>
         programIx == 7 &&
           metas == #[{ acc := source, signer := false, writable := true },
             { acc := destination, signer := false, writable := true },
             { acc := authority, signer := true, writable := false }] &&
           data.size == 2 && data[0]? == some (.u8le (.lit 3)) &&
           (match data[1]? with
            | some (ProofForge.Svm.Ops.CpiWord.u64le _) => true
            | _ => false) &&
           actualSeeds == seeds
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveUncheckedTransfer source destination authority seeds thenOps ||
            opsHaveUncheckedTransfer source destination authority seeds elseOps
      | .forBody _ body => opsHaveUncheckedTransfer source destination authority seeds body
      | _ => false

/-- Unsigned classic Token Transfer (tag 3) with an ordinary signer authority. -/
private partial def opsHaveUnsignedUncheckedTransfer
    (source destination authority : Nat) (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .invoke programIx metas data actualSeeds bump =>
         programIx == 7 && bump.isNone && actualSeeds.isEmpty &&
           metas == #[{ acc := source, signer := false, writable := true },
             { acc := destination, signer := false, writable := true },
             { acc := authority, signer := true, writable := false }] &&
           data.size == 2 && data[0]? == some (.u8le (.lit 3)) &&
           (match data[1]? with
            | some (ProofForge.Svm.Ops.CpiWord.u64le _) => true
            | _ => false)
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveUnsignedUncheckedTransfer source destination authority thenOps ||
            opsHaveUnsignedUncheckedTransfer source destination authority elseOps
      | .forBody _ body => opsHaveUnsignedUncheckedTransfer source destination authority body
      | _ => false

private partial def opsHaveFifoCancelCall
    (predicate : ProofForge.Svm.FifoCancel.Call ProofForge.Svm.Ops.Val → Bool)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    (match op with
     | .component (.fifoCancel call) => predicate call
     | _ => false) ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveFifoCancelCall predicate thenOps || opsHaveFifoCancelCall predicate elseOps
      | .forBody _ body => opsHaveFifoCancelCall predicate body
      | _ => false

private partial def fifoCancelCalls (ops : Array ProofForge.Svm.IR.Op) : List String :=
  ops.toList.flatMap fun op =>
    match op with
    | .component (.fifoCancel call) => [call.canonical (fun value => toString (repr value))]
    | .ite _ _ _ thenOps elseOps => fifoCancelCalls thenOps ++ fifoCancelCalls elseOps
    | .forBody _ body => fifoCancelCalls body
    | _ => []

private partial def valHasFifoCancelQuery
    (predicate : ProofForge.Svm.FifoCancel.Query → Bool) : ProofForge.Svm.Ops.Val → Bool
  | .field base _ | .bitNot base => valHasFifoCancelQuery predicate base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valHasFifoCancelQuery predicate lhs || valHasFifoCancelQuery predicate rhs
  | .indexGet base _ index _ _ =>
      valHasFifoCancelQuery predicate base || valHasFifoCancelQuery predicate index
  | .select _ lhs rhs thenValue elseValue =>
      valHasFifoCancelQuery predicate lhs || valHasFifoCancelQuery predicate rhs ||
        valHasFifoCancelQuery predicate thenValue || valHasFifoCancelQuery predicate elseValue
  | .ext (.component (.fifoCancel query)) operands =>
      predicate query || operands.any (valHasFifoCancelQuery predicate)
  | .ext _ operands => operands.any (valHasFifoCancelQuery predicate)
  | _ => false

private partial def opsHaveFifoCancelQuery
    (predicate : ProofForge.Svm.FifoCancel.Query → Bool)
    (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    let has := valHasFifoCancelQuery predicate
    let here :=
      match op with
      | .letLocal _ value | .setLocal _ value | .forAccum _ value _
      | .storeField _ value | .okState value | .returnU64 value | .returnState value => has value
      | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
      | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
      | .indexSet _ lhs rhs _ _ => has lhs || has rhs
      | .invoke _ _ data _ bump =>
          data.any (fun item => item.value?.any has) || bump.any has
      | .component call => call.values.any has
      | _ => false
    here ||
      match op with
      | .ite _ _ _ thenOps elseOps =>
          opsHaveFifoCancelQuery predicate thenOps || opsHaveFifoCancelQuery predicate elseOps
      | .forBody _ body => opsHaveFifoCancelQuery predicate body
      | _ => false

private partial def opsHaveInvoke (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.any fun op =>
    match op with
    | .invoke .. => true
    | .ite _ _ _ thenOps elseOps => opsHaveInvoke thenOps || opsHaveInvoke elseOps
    | .forBody _ body => opsHaveInvoke body
    | _ => false

private def fifoCancelConfigMatches
    (root links parent price sequence owner size locked free : Nat) (bid : Bool)
    (config : ProofForge.Svm.FifoCancel.Config) : Bool :=
  match config.map with
  | .key4 .. => false
  | .fifo actualRoot tree =>
      actualRoot == root && tree.links.region.account == 2 &&
        tree.links.firstWord == links && tree.parentColor.firstWord == parent &&
        tree.price.firstWord == price && tree.sequence.firstWord == sequence &&
        config.owner.firstWord == owner && config.size.firstWord == size &&
        config.locked.firstWord == locked && config.free.firstWord == free &&
        tree.links.region.strideWords == 8 && tree.links.region.capacity == 512 &&
        tree.bid == bid && config.recorder.logAccount == 0 &&
        config.recorder.selfEntryTag == 15 && config.recorder.maxRecords == 32 &&
        config.collateral == if bid then .quote 104 105 else .base

private def fifoCancelSideMatches
    (root links parent price sequence owner size locked free : Nat) (bid : Bool) :
    ProofForge.Svm.FifoCancel.Call ProofForge.Svm.Ops.Val → Bool
  | .cancelSide config _ =>
      fifoCancelConfigMatches root links parent price sequence owner size locked free bid config
  | _ => false

private def fifoCancelUpToMatches
    (root links parent price sequence owner size locked free : Nat) (bid claim : Bool) :
    ProofForge.Svm.FifoCancel.Call ProofForge.Svm.Ops.Val → Bool
  | .cancelUpTo config _ _ _ _ actualClaim =>
      actualClaim == claim &&
        fifoCancelConfigMatches root links parent price sequence owner size locked free bid config
  | _ => false

private partial def cancelTraceValue : ProofForge.Svm.Ops.Val → List Nat
  | .field base _ | .bitNot base => cancelTraceValue base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs => cancelTraceValue lhs ++ cancelTraceValue rhs
  | .indexGet base _ index _ _ => cancelTraceValue base ++ cancelTraceValue index
  | .select _ lhs rhs thenValue elseValue =>
      cancelTraceValue lhs ++ cancelTraceValue rhs ++ cancelTraceValue thenValue ++
        cancelTraceValue elseValue
  | .ext (.component (.accountStorage query)) operands =>
      let marker := match query with
        | .key4RbTreeValid tree => if tree.links.region.account == 2 then [1] else []
        | .fifoRbTreeValid tree =>
            if tree.links.region.account != 2 then [] else if tree.bid then [2] else [3]
        | _ => []
      marker ++ operands.toList.flatMap cancelTraceValue
  | .ext (.component (.fifoCancel query)) operands =>
      let marker := match query with
        | .quoteReleased => [7]
        | .baseReleased => [8]
        | .eventCount => [9]
      marker ++ operands.toList.flatMap cancelTraceValue
  | .ext _ operands => operands.toList.flatMap cancelTraceValue
  | _ => []

private partial def cancelTraceOps (ops : Array ProofForge.Svm.IR.Op) : List Nat :=
  ops.toList.flatMap fun op =>
    match op with
    | .letLocal _ value | .setLocal _ value | .forAccum _ value _
    | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
        cancelTraceValue value
    | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
    | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .indexSet _ lhs rhs _ _ =>
        cancelTraceValue lhs ++ cancelTraceValue rhs
    | .ite _ lhs rhs thenOps elseOps =>
        cancelTraceValue lhs ++ cancelTraceValue rhs ++ cancelTraceOps thenOps ++
          cancelTraceOps elseOps
    | .forBody _ body => cancelTraceOps body
    | .component (.fifoCancel call) =>
        match call with
        | .begin => [4]
        | .cancelSide config _ => if config.map.rootWord == 110 then [5] else [6]
        | .cancelUpTo config .. => if config.map.rootWord == 110 then [16] else [17]
        | .finish => [13]
    | .component (.batchRecorder (.finish _)) => [14]
    | .component (.accountStorage (.writeWord field _ _)) =>
        if field.firstWord == 8321 then [10]
        else if field.firstWord == 8323 then [12]
        else []
    | .invoke _ metas data _ bump =>
        let values := data.toList.flatMap fun word =>
          word.value?.map cancelTraceValue |>.getD []
        let values := values ++ (bump.map cancelTraceValue).getD []
        let marker := match metas[0]? with
          | some entry => if entry.acc == 6 then [11] else if entry.acc == 5 then [15] else []
          | none => []
        values ++ marker
    | _ => []

private def traceBefore (first second : Nat) : List Nat → Bool
  | [] => false
  | item :: rest => if item == first then rest.contains second else traceBefore first second rest

elab "#pf_guard_phoenix_v1_profile" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.PhoenixV1Profile none with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless ProofForge.Svm.IR.dataLen program == 16 &&
      ProofForge.Svm.IR.generatedAccountCount program == 2 &&
      ProofForge.Svm.IR.cpiAccountCount program == 9 do
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
  let some findTrader := program.methods.find? (·.ixName == "findTrader128")
    | throwError "missing findTrader128"
  let some findBid := program.methods.find? (·.ixName == "findBid512")
    | throwError "missing findBid512"
  let some findAsk := program.methods.find? (·.ixName == "findAsk512")
    | throwError "missing findAsk512"
  let some cursorBid := program.methods.find? (·.ixName == "cursorBid512")
    | throwError "missing cursorBid512"
  let some cursorAsk := program.methods.find? (·.ixName == "cursorAsk512")
    | throwError "missing cursorAsk512"
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
  let some reduceAsk := program.methods.find? (·.ixName == "reduceAskFreeFunds512")
    | throwError "missing reduceAskFreeFunds512"
  let some reduceBid := program.methods.find? (·.ixName == "reduceBidFreeFunds512")
    | throwError "missing reduceBidFreeFunds512"
  let some placeRaw := program.methods.find? (·.ixName == "placeLimitOrderWithFreeFunds")
    | throwError s!"missing raw PlaceLimitOrderWithFreeFunds: {repr (program.methods.map (·.ixName))}"
  let some placeLimitRaw :=
      program.methods.find? (·.ixName == "placeLimitOrderWithFreeFundsLimit")
    | throwError "missing raw Limit OrderPacket handler"
  let some reduceRaw := program.methods.find? (·.ixName == "reduceOrderWithFreeFunds")
    | throwError "missing raw ReduceOrderWithFreeFunds"
  let some reduceWithdrawRaw := program.methods.find? (·.ixName == "reduceOrder")
    | throwError "missing raw ReduceOrder"
  let some cancelAllRaw := program.methods.find? (·.ixName == "cancelAllOrders")
    | throwError "missing raw CancelAllOrders"
  let some cancelAllFreeRaw :=
      program.methods.find? (·.ixName == "cancelAllOrdersWithFreeFunds")
    | throwError "missing raw CancelAllOrdersWithFreeFunds"
  let some cancelUpToRaw := program.methods.find? (·.ixName == "cancelUpToOrders")
    | throwError "missing raw CancelUpTo"
  let some cancelUpToFreeRaw :=
      program.methods.find? (·.ixName == "cancelUpToOrdersWithFreeFunds")
    | throwError "missing raw CancelUpToWithFreeFunds"
  let some cancelByIdRaw := program.methods.find? (·.ixName == "cancelMultipleOrdersById")
    | throwError "missing raw CancelMultipleOrdersById"
  let some cancelByIdFreeRaw :=
      program.methods.find? (·.ixName == "cancelMultipleOrdersByIdWithFreeFunds")
    | throwError "missing raw CancelMultipleOrdersByIdWithFreeFunds"
  let some withdrawFundsRaw := program.methods.find? (·.ixName == "withdrawFunds")
    | throwError "missing raw WithdrawFunds"
  let some depositFundsRaw := program.methods.find? (·.ixName == "depositFunds")
    | throwError "missing raw DepositFunds"
  match placeRaw.entry with
  | .raw entry =>
      unless placeRaw.kind == .get && placeRaw.retCount == 3 &&
          entry.tag == 3 && entry.variant == some 0 && entry.accountCount == 5 &&
          entry.programAccount == 0 &&
          entry.paramWidths == #[1, 8, 8, 8, 8, 1, 1, 1, 1, 1] &&
          entry.dataLen == 40 && entry.returnWidths == #[4, 8, 8] &&
          entry.returnDataLen == 20 do
        throwError s!"wrong raw PlaceLimitOrderWithFreeFunds adapter: {repr entry}"
  | .generated => throwError "PlaceLimitOrderWithFreeFunds lost its raw adapter"
  match placeLimitRaw.entry with
  | .raw entry =>
      unless placeLimitRaw.kind == .get && placeLimitRaw.retCount == 4 &&
          entry.tag == 3 && entry.variant == some 1 && entry.accountCount == 5 &&
          entry.programAccount == 0 &&
          entry.paramWidths == #[1, 8, 8, 1, 1, 8, 8, 8, 1, 1, 1, 1] &&
          entry.dataLen == 49 && entry.returnWidths == #[4, 8, 8] &&
          entry.returnDataLen == 20 && entry.optionalReturnData do
        throwError s!"wrong raw Limit OrderPacket adapter: {repr entry}"
  | .generated => throwError "Limit OrderPacket lost its raw adapter"
  let placeCfg ←
    match placeRaw.toCFG with
    | .ok graph => pure graph
    | .error reason => throwError reason
  unless placeCfg.blocks.any fun block =>
      match block.terminator with
      | .exit (.returnU64s values) => values.size == 3
      | _ => false do
    throwError "PlaceLimitOrderWithFreeFunds did not use the generic three-scalar CFG return"
  match reduceRaw.entry with
  | .raw entry =>
      unless reduceRaw.kind == .get && entry.tag == 5 && entry.accountCount == 4 &&
          entry.programAccount == 0 && entry.paramWidths == #[1, 8, 8, 8] &&
          entry.dataLen == 26 do
        throwError s!"wrong raw ReduceOrderWithFreeFunds adapter: {repr entry}"
  | .generated => throwError "ReduceOrderWithFreeFunds lost its raw adapter"
  match reduceWithdrawRaw.entry with
  | .raw entry =>
      unless reduceWithdrawRaw.kind == .get && entry.tag == 4 && entry.accountCount == 9 &&
          entry.programAccount == 0 && entry.paramWidths == #[1, 8, 8, 8] &&
          entry.dataLen == 26 do
        throwError s!"wrong raw ReduceOrder adapter: {repr entry}"
  | .generated => throwError "ReduceOrder lost its raw adapter"
  match cancelAllRaw.entry with
  | .raw entry =>
      unless cancelAllRaw.kind == .get && entry.tag == 6 && entry.accountCount == 9 &&
          entry.programAccount == 0 && entry.paramWidths.isEmpty && entry.dataLen == 1 do
        throwError s!"wrong raw CancelAllOrders adapter: {repr entry}"
  | .generated => throwError "CancelAllOrders lost its raw adapter"
  match cancelAllFreeRaw.entry with
  | .raw entry =>
      unless cancelAllFreeRaw.kind == .get && entry.tag == 7 && entry.accountCount == 4 &&
          entry.programAccount == 0 && entry.paramWidths.isEmpty && entry.dataLen == 1 do
        throwError s!"wrong raw CancelAllOrdersWithFreeFunds adapter: {repr entry}"
  | .generated => throwError "CancelAllOrdersWithFreeFunds lost its raw adapter"
  match cancelUpToRaw.entry with
  | .raw entry =>
      unless cancelUpToRaw.kind == .get && entry.tag == 8 && entry.accountCount == 9 &&
          entry.programAccount == 0 && entry.paramWidths == #[1, 1, 8, 1, 4, 1, 4] &&
          entry.optionWidths == #[8, 4, 4] && entry.fixedParamCount == 1 &&
          entry.minDataLen == 5 && entry.maxDataLen == 21 do
        throwError s!"wrong raw CancelUpTo adapter: {repr entry}"
  | .generated => throwError "CancelUpTo lost its raw adapter"
  match cancelUpToFreeRaw.entry with
  | .raw entry =>
      unless cancelUpToFreeRaw.kind == .get && entry.tag == 9 && entry.accountCount == 4 &&
          entry.programAccount == 0 && entry.paramWidths == #[1, 1, 8, 1, 4, 1, 4] &&
          entry.optionWidths == #[8, 4, 4] && entry.fixedParamCount == 1 &&
          entry.minDataLen == 5 && entry.maxDataLen == 21 do
        throwError s!"wrong raw CancelUpToWithFreeFunds adapter: {repr entry}"
  | .generated => throwError "CancelUpToWithFreeFunds lost its raw adapter"
  match cancelByIdRaw.entry with
  | .raw entry =>
      unless cancelByIdRaw.kind == .get && entry.tag == 10 && entry.accountCount == 9 &&
          entry.programAccount == 0 && entry.paramCount == 1 &&
          entry.usesSchemaBorsh && entry.minDataLen == 5 && entry.maxDataLen == 141 do
        throwError s!"wrong raw CancelMultipleOrdersById adapter: {repr entry}"
  | .generated => throwError "CancelMultipleOrdersById lost its raw adapter"
  match cancelByIdFreeRaw.entry with
  | .raw entry =>
      unless cancelByIdFreeRaw.kind == .get && entry.tag == 11 && entry.accountCount == 4 &&
          entry.programAccount == 0 && entry.paramCount == 1 &&
          entry.usesSchemaBorsh && entry.minDataLen == 5 && entry.maxDataLen == 141 do
        throwError s!"wrong raw CancelMultipleOrdersByIdWithFreeFunds adapter: {repr entry}"
  | .generated => throwError "CancelMultipleOrdersByIdWithFreeFunds lost its raw adapter"
  match withdrawFundsRaw.entry with
  | .raw entry =>
      unless withdrawFundsRaw.kind == .get && entry.tag == 12 && entry.accountCount == 9 &&
          entry.programAccount == 0 && entry.paramWidths == #[8, 8] &&
          entry.dataLen == 17 do
        throwError s!"wrong raw WithdrawFunds adapter: {repr entry}"
  | .generated => throwError "WithdrawFunds lost its raw adapter"
  match depositFundsRaw.entry with
  | .raw entry =>
      unless depositFundsRaw.kind == .get && entry.tag == 13 && entry.accountCount == 9 &&
          entry.programAccount == 0 && entry.paramWidths == #[8, 8] &&
          entry.dataLen == 17 do
        throwError s!"wrong raw DepositFunds adapter: {repr entry}"
  | .generated => throwError "DepositFunds lost its raw adapter"
  unless opsHaveIntrinsic (· == .isWritableN 0) placeRaw.ops &&
      opsHaveIntrinsic (· == .isWritableN 1) placeRaw.ops &&
      opsHaveIntrinsic (· == .isWritableN 3) placeRaw.ops &&
      opsHaveIntrinsic (· == .isWritableN 4) placeRaw.ops &&
      opsHaveIntrinsic (· == .ownerIsSelf 4) placeRaw.ops &&
      opsHaveIntrinsic (· == .signerKeyN 3) placeRaw.ops &&
      opsHaveIntrinsic (· == .checkPdaSeeds 0 #[.ascii "log"]) placeRaw.ops &&
      opsHaveIntrinsic
        (· == .checkPdaSeeds 3 #[.ascii "seat", .accKey 1, .accKey 2]) placeRaw.ops &&
      opsHaveDataWord 4 0 placeRaw.ops && opsHaveDataWord 4 9 placeRaw.ops &&
      opsHaveIndexedDataWord 2 1 1 1 placeRaw.ops &&
      opsHaveIndexedDataWord 2 34 1 1 placeRaw.ops &&
      opsHaveIndexedDataWord 2 106 1 1 placeRaw.ops &&
      opsHaveIndexedDataWord 2 112 1 1 placeRaw.ops &&
      opsHaveIndexedDataWord 2 4212 1 1 placeRaw.ops &&
      opsHaveAccountQuery (fun
        | .key4RbTreeValid tree => tree.links.region.account == 2
        | _ => false) placeRaw.ops &&
      opsHaveAccountQuery (fun
        | .fifoRbTreeValid tree => tree.links.region.account == 2 && tree.bid
        | _ => false) placeRaw.ops &&
      opsHaveAccountQuery (fun
        | .fifoRbTreeValid tree => tree.links.region.account == 2 && !tree.bid
        | _ => false) placeRaw.ops &&
      opsHaveAccountQuery (fun
        | .key4Find 8310 tree => tree.links.region.account == 2
        | _ => false) placeRaw.ops &&
      opsHaveAccountQuery (fun
        | .fifoFind 110 tree => tree.links.region.account == 2 && tree.bid
        | .fifoFind 4210 tree => tree.links.region.account == 2 && !tree.bid
        | _ => false) placeRaw.ops &&
      opsHaveRbTreeOrderInsert 2 110 114 115 116 117 8 512 true placeRaw.ops &&
      opsHaveRbTreeOrderInsert 2 4210 4214 4215 4216 4217 8 512 false placeRaw.ops &&
      opsHaveOneBasedDataWordSetAt 2 8320 18 128 placeRaw.ops &&
      opsHaveOneBasedDataWordSetAt 2 8321 18 128 placeRaw.ops &&
      opsHaveOneBasedDataWordSetAt 2 8322 18 128 placeRaw.ops &&
      opsHaveOneBasedDataWordSetAt 2 8323 18 128 placeRaw.ops &&
      opsHaveDataWordSetAt 2 106 1 1 placeRaw.ops &&
      opsHaveDataWordSetAt 2 34 1 1 placeRaw.ops &&
      opsHaveRawReduceHeader 3 placeRaw.ops && opsHaveRawPlaceRecord placeRaw.ops &&
      opsHaveRawReduceFinish placeRaw.ops && !opsHaveInvoke placeRaw.ops do
    throwError "raw PlaceLimitOrderWithFreeFunds bounded composition is incomplete"
  unless opsHaveIntrinsic (· == .isWritableN 1) reduceRaw.ops &&
      opsHaveIntrinsic (· == .isWritableN 3) reduceRaw.ops &&
      opsHaveIntrinsic (· == .signerKeyN 3) reduceRaw.ops &&
      opsHaveIntrinsic (· == .checkPdaSeeds 0 #[.ascii "log"]) reduceRaw.ops &&
      opsHaveDataWord 2 34 reduceRaw.ops &&
      opsHaveAccountQuery (fun
        | .key4RbTreeValid tree => tree.links.region.account == 2
        | _ => false) reduceRaw.ops &&
      opsHaveAccountQuery (fun
        | .key4Find 8310 tree => tree.links.region.account == 2
        | _ => false) reduceRaw.ops &&
      opsHaveAccountQuery (fun
        | .fifoFind 110 tree => tree.links.region.account == 2 && tree.bid
        | .fifoFind 4210 tree => tree.links.region.account == 2 && !tree.bid
        | _ => false) reduceRaw.ops &&
      opsHaveRbTreeOrderRemove 2 110 114 115 116 117 8 512 true reduceRaw.ops &&
      opsHaveRbTreeOrderRemove 2 4210 4214 4215 4216 4217 8 512 false reduceRaw.ops &&
      opsHaveOneBasedDataWordSetAt 2 119 8 512 reduceRaw.ops &&
      opsHaveOneBasedDataWordSetAt 2 4219 8 512 reduceRaw.ops &&
      opsHaveDataWordSetAt 2 34 1 1 reduceRaw.ops &&
      opsHaveRawReduceHeader 5 reduceRaw.ops && opsHaveRawReduceRecord reduceRaw.ops &&
      opsHaveRawReduceFinish reduceRaw.ops do
    throwError s!"raw ReduceOrderWithFreeFunds composition incomplete: " ++
      s!"w1={opsHaveIntrinsic (· == .isWritableN 1) reduceRaw.ops}, " ++
      s!"w3={opsHaveIntrinsic (· == .isWritableN 3) reduceRaw.ops}, " ++
      s!"signer={opsHaveIntrinsic (· == .signerKeyN 3) reduceRaw.ops}, " ++
      s!"pda={opsHaveIntrinsic (· == .checkPdaSeeds 0 #[.ascii "log"]) reduceRaw.ops}, " ++
      s!"seq={opsHaveDataWord 2 34 reduceRaw.ops}, " ++
      s!"seqWrite={opsHaveDataWordSetAt 2 34 1 1 reduceRaw.ops}, " ++
      s!"bidRemove={opsHaveRbTreeOrderRemove 2 110 114 115 116 117 8 512 true reduceRaw.ops}, " ++
      s!"askRemove={opsHaveRbTreeOrderRemove 2 4210 4214 4215 4216 4217 8 512 false reduceRaw.ops}, " ++
      s!"header={opsHaveRawReduceHeader 5 reduceRaw.ops}, " ++
      s!"record={opsHaveRawReduceRecord reduceRaw.ops}, " ++
      s!"finish={opsHaveRawReduceFinish reduceRaw.ops}"
  let baseSeeds : Array ProofForge.Svm.Ops.PdaSeed :=
    #[.ascii "vault", .accKey 1, .accData 1 48 32]
  let quoteSeeds : Array ProofForge.Svm.Ops.PdaSeed :=
    #[.ascii "vault", .accKey 1, .accData 1 128 32]
  unless opsHaveIntrinsic (· == .isWritableN 8) reduceWithdrawRaw.ops &&
      opsHaveIntrinsic (· == .isExecutableN 8) reduceWithdrawRaw.ops &&
      opsHaveIntrinsic (· == .signerKeyN 3) reduceWithdrawRaw.ops &&
      opsHaveIntrinsic (· == .checkPdaSeeds 0 #[.ascii "log"]) reduceWithdrawRaw.ops &&
      opsHaveDataWord 2 1 reduceWithdrawRaw.ops &&
      opsHaveDataWord 2 5 reduceWithdrawRaw.ops &&
      opsHaveDataWord 2 6 reduceWithdrawRaw.ops &&
      opsHaveDataWord 2 14 reduceWithdrawRaw.ops &&
      opsHaveDataWord 2 15 reduceWithdrawRaw.ops &&
      opsHaveDataWord 2 16 reduceWithdrawRaw.ops &&
      opsHaveDataWord 2 24 reduceWithdrawRaw.ops &&
      opsHaveOneBasedDataWordSetAt 2 8321 18 128 reduceWithdrawRaw.ops &&
      opsHaveOneBasedDataWordSetAt 2 8323 18 128 reduceWithdrawRaw.ops &&
      opsHaveUncheckedTransfer 5 3 5 baseSeeds reduceWithdrawRaw.ops &&
      opsHaveUncheckedTransfer 6 4 6 quoteSeeds reduceWithdrawRaw.ops &&
      opsHaveRawReduceHeader 4 reduceWithdrawRaw.ops &&
      opsHaveRawReduceRecord reduceWithdrawRaw.ops &&
      opsHaveRawReduceFinish reduceWithdrawRaw.ops do
    throwError s!"raw ReduceOrder composition incomplete: " ++
      s!"w8={opsHaveIntrinsic (· == .isWritableN 8) reduceWithdrawRaw.ops}, " ++
      s!"exec8={opsHaveIntrinsic (· == .isExecutableN 8) reduceWithdrawRaw.ops}, " ++
      s!"signer={opsHaveIntrinsic (· == .signerKeyN 3) reduceWithdrawRaw.ops}, " ++
      s!"pda={opsHaveIntrinsic (· == .checkPdaSeeds 0 #[.ascii "log"]) reduceWithdrawRaw.ops}, " ++
      s!"status={opsHaveDataWord 2 1 reduceWithdrawRaw.ops}, " ++
      s!"baseBump={opsHaveDataWord 2 5 reduceWithdrawRaw.ops}, " ++
      s!"baseMint={opsHaveDataWord 2 6 reduceWithdrawRaw.ops}, " ++
      s!"baseLot={opsHaveDataWord 2 14 reduceWithdrawRaw.ops}, " ++
      s!"quoteBump={opsHaveDataWord 2 15 reduceWithdrawRaw.ops}, " ++
      s!"quoteMint={opsHaveDataWord 2 16 reduceWithdrawRaw.ops}, " ++
      s!"quoteLot={opsHaveDataWord 2 24 reduceWithdrawRaw.ops}, " ++
      s!"claimBase={opsHaveOneBasedDataWordSetAt 2 8321 18 128 reduceWithdrawRaw.ops}, " ++
      s!"claimQuote={opsHaveOneBasedDataWordSetAt 2 8323 18 128 reduceWithdrawRaw.ops}, " ++
      s!"baseTransfer={opsHaveUncheckedTransfer 5 3 5 baseSeeds reduceWithdrawRaw.ops}, " ++
      s!"quoteTransfer={opsHaveUncheckedTransfer 6 4 6 quoteSeeds reduceWithdrawRaw.ops}, " ++
      s!"header={opsHaveRawReduceHeader 4 reduceWithdrawRaw.ops}, " ++
      s!"record={opsHaveRawReduceRecord reduceWithdrawRaw.ops}, " ++
      s!"finish={opsHaveRawReduceFinish reduceWithdrawRaw.ops}"
  let hasCancelValidators (ops : Array ProofForge.Svm.IR.Op) :=
    opsHaveAccountQuery (fun
        | .key4RbTreeValid tree => tree.links.region.account == 2 &&
            tree.links.firstWord == 8314 && tree.links.region.capacity == 128
        | _ => false) ops &&
      opsHaveAccountQuery (fun
        | .fifoRbTreeValid tree => tree.links.region.account == 2 &&
            tree.links.firstWord == 114 && tree.links.region.capacity == 512 && tree.bid
        | _ => false) ops &&
      opsHaveAccountQuery (fun
        | .fifoRbTreeValid tree => tree.links.region.account == 2 &&
            tree.links.firstWord == 4214 && tree.links.region.capacity == 512 && !tree.bid
        | _ => false) ops
  let hasCancelComponents (ops : Array ProofForge.Svm.IR.Op) :=
    opsHaveFifoCancelCall (fun | .begin => true | _ => false) ops &&
      opsHaveFifoCancelCall
        (fifoCancelSideMatches 110 114 115 116 117 118 119 8320 8321 true) ops &&
      opsHaveFifoCancelCall
        (fifoCancelSideMatches 4210 4214 4215 4216 4217 4218 4219 8322 8323 false) ops &&
      opsHaveFifoCancelCall (fun | .finish => true | _ => false) ops
  let hasCancelUpToComponents (claim : Bool) (ops : Array ProofForge.Svm.IR.Op) :=
    opsHaveFifoCancelCall (fun | .begin => true | _ => false) ops &&
      opsHaveFifoCancelCall
        (fifoCancelUpToMatches 110 114 115 116 117 118 119 8320 8321 true claim) ops &&
      opsHaveFifoCancelCall
        (fifoCancelUpToMatches 4210 4214 4215 4216 4217 4218 4219 8322 8323 false claim) ops &&
      opsHaveFifoCancelCall (fun | .finish => true | _ => false) ops
  unless hasCancelValidators cancelAllFreeRaw.ops && hasCancelComponents cancelAllFreeRaw.ops &&
      opsHaveAccountQuery (fun
        | .key4Find 8310 tree => tree.links.region.account == 2
        | _ => false) cancelAllFreeRaw.ops &&
      opsHaveDataWordSetAt 2 34 1 1 cancelAllFreeRaw.ops &&
      opsHaveRawReduceHeader 7 cancelAllFreeRaw.ops &&
      opsHaveRawReduceFinish cancelAllFreeRaw.ops &&
      !opsHaveInvoke cancelAllFreeRaw.ops && !opsHaveDataWord 2 1 cancelAllFreeRaw.ops do
    throwError s!"raw CancelAllOrdersWithFreeFunds component composition is incomplete: " ++
      s!"validators={hasCancelValidators cancelAllFreeRaw.ops}, " ++
      s!"components={hasCancelComponents cancelAllFreeRaw.ops}, " ++
      s!"begin={opsHaveFifoCancelCall (fun | .begin => true | _ => false) cancelAllFreeRaw.ops}, " ++
      s!"bid={opsHaveFifoCancelCall (fifoCancelSideMatches 110 114 115 116 117 118 119 8320 8321 true) cancelAllFreeRaw.ops}, " ++
      s!"ask={opsHaveFifoCancelCall (fifoCancelSideMatches 4210 4214 4215 4216 4217 4218 4219 8322 8323 false) cancelAllFreeRaw.ops}, " ++
      s!"finish={opsHaveFifoCancelCall (fun | .finish => true | _ => false) cancelAllFreeRaw.ops}, " ++
      s!"trader={opsHaveAccountQuery (fun | .key4Find 8310 tree => tree.links.region.account == 2 | _ => false) cancelAllFreeRaw.ops}, " ++
      s!"sequence={opsHaveDataWordSetAt 2 34 1 1 cancelAllFreeRaw.ops}, " ++
      s!"header={opsHaveRawReduceHeader 7 cancelAllFreeRaw.ops}, " ++
      s!"finishBatch={opsHaveRawReduceFinish cancelAllFreeRaw.ops}, " ++
      s!"invoke={opsHaveInvoke cancelAllFreeRaw.ops}, status={opsHaveDataWord 2 1 cancelAllFreeRaw.ops}, " ++
      s!"calls={String.intercalate ";" (fifoCancelCalls cancelAllFreeRaw.ops)}"
  unless hasCancelValidators cancelAllRaw.ops && hasCancelComponents cancelAllRaw.ops &&
      opsHaveFifoCancelQuery (· == .quoteReleased) cancelAllRaw.ops &&
      opsHaveFifoCancelQuery (· == .baseReleased) cancelAllRaw.ops &&
      opsHaveDataWord 2 1 cancelAllRaw.ops && opsHaveDataWord 2 14 cancelAllRaw.ops &&
      opsHaveDataWord 2 24 cancelAllRaw.ops &&
      opsHaveOneBasedDataWordSetAt 2 8321 18 128 cancelAllRaw.ops &&
      opsHaveOneBasedDataWordSetAt 2 8323 18 128 cancelAllRaw.ops &&
      opsHaveUncheckedTransfer 6 4 6 quoteSeeds cancelAllRaw.ops &&
      opsHaveUncheckedTransfer 5 3 5 baseSeeds cancelAllRaw.ops &&
      opsHaveRawReduceHeader 6 cancelAllRaw.ops &&
      opsHaveRawReduceFinish cancelAllRaw.ops do
    throwError "raw CancelAllOrders component/query/withdraw composition is incomplete"
  unless hasCancelValidators cancelUpToFreeRaw.ops &&
      hasCancelUpToComponents false cancelUpToFreeRaw.ops &&
      opsHaveAccountQuery (fun
        | .key4Find 8310 tree => tree.links.region.account == 2
        | _ => false) cancelUpToFreeRaw.ops &&
      opsHaveDataWord 2 112 cancelUpToFreeRaw.ops &&
      opsHaveDataWord 2 4212 cancelUpToFreeRaw.ops &&
      opsHaveDataWordSetAt 2 34 1 1 cancelUpToFreeRaw.ops &&
      opsHaveRawReduceHeader 9 cancelUpToFreeRaw.ops &&
      opsHaveRawReduceFinish cancelUpToFreeRaw.ops &&
      !opsHaveInvoke cancelUpToFreeRaw.ops && !opsHaveDataWord 2 1 cancelUpToFreeRaw.ops do
    throwError s!"raw CancelUpToWithFreeFunds bounded component composition is incomplete: " ++
      s!"validators={hasCancelValidators cancelUpToFreeRaw.ops}, " ++
      s!"components={hasCancelUpToComponents false cancelUpToFreeRaw.ops}, " ++
      s!"begin={opsHaveFifoCancelCall (fun | .begin => true | _ => false) cancelUpToFreeRaw.ops}, " ++
      s!"bid={opsHaveFifoCancelCall (fifoCancelUpToMatches 110 114 115 116 117 118 119 8320 8321 true false) cancelUpToFreeRaw.ops}, " ++
      s!"ask={opsHaveFifoCancelCall (fifoCancelUpToMatches 4210 4214 4215 4216 4217 4218 4219 8322 8323 false false) cancelUpToFreeRaw.ops}, " ++
      s!"close={opsHaveFifoCancelCall (fun | .finish => true | _ => false) cancelUpToFreeRaw.ops}, " ++
      s!"sizeBid={opsHaveDataWord 2 112 cancelUpToFreeRaw.ops}, " ++
      s!"sizeAsk={opsHaveDataWord 2 4212 cancelUpToFreeRaw.ops}, " ++
      s!"seq={opsHaveDataWordSetAt 2 34 1 1 cancelUpToFreeRaw.ops}, " ++
      s!"header={opsHaveRawReduceHeader 9 cancelUpToFreeRaw.ops}, " ++
      s!"finish={opsHaveRawReduceFinish cancelUpToFreeRaw.ops}, " ++
      s!"invoke={opsHaveInvoke cancelUpToFreeRaw.ops}, status={opsHaveDataWord 2 1 cancelUpToFreeRaw.ops}"
  unless hasCancelValidators cancelUpToRaw.ops &&
      hasCancelUpToComponents true cancelUpToRaw.ops &&
      opsHaveFifoCancelQuery (· == .quoteReleased) cancelUpToRaw.ops &&
      opsHaveFifoCancelQuery (· == .baseReleased) cancelUpToRaw.ops &&
      opsHaveDataWord 2 1 cancelUpToRaw.ops && opsHaveDataWord 2 14 cancelUpToRaw.ops &&
      opsHaveDataWord 2 24 cancelUpToRaw.ops &&
      !opsHaveOneBasedDataWordSetAt 2 8321 18 128 cancelUpToRaw.ops &&
      !opsHaveOneBasedDataWordSetAt 2 8323 18 128 cancelUpToRaw.ops &&
      opsHaveUncheckedTransfer 6 4 6 quoteSeeds cancelUpToRaw.ops &&
      opsHaveUncheckedTransfer 5 3 5 baseSeeds cancelUpToRaw.ops &&
      opsHaveRawReduceHeader 8 cancelUpToRaw.ops &&
      opsHaveRawReduceFinish cancelUpToRaw.ops do
    throwError "raw CancelUpTo bounded component/query/withdraw composition is incomplete"
  unless opsHaveIntrinsic (· == .isWritableN 1) cancelByIdFreeRaw.ops &&
      opsHaveIntrinsic (· == .isWritableN 2) cancelByIdFreeRaw.ops &&
      opsHaveIntrinsic (· == .signerKeyN 3) cancelByIdFreeRaw.ops &&
      opsHaveIntrinsic (· == .checkPdaSeeds 0 #[.ascii "log"]) cancelByIdFreeRaw.ops &&
      opsHaveDataWordSetAt 2 34 1 1 cancelByIdFreeRaw.ops &&
      opsHaveRawReduceHeader 11 cancelByIdFreeRaw.ops &&
      opsHaveRawReduceFinish cancelByIdFreeRaw.ops &&
      !opsHaveInvoke cancelByIdFreeRaw.ops do
    throwError "raw CancelMultipleOrdersByIdWithFreeFunds composition is incomplete"
  unless opsHaveIntrinsic (· == .signerKeyN 3) cancelByIdRaw.ops &&
      opsHaveDataWord 2 1 cancelByIdRaw.ops &&
      opsHaveUncheckedTransfer 6 4 6 quoteSeeds cancelByIdRaw.ops &&
      opsHaveUncheckedTransfer 5 3 5 baseSeeds cancelByIdRaw.ops &&
      opsHaveRawReduceHeader 10 cancelByIdRaw.ops &&
      opsHaveRawReduceFinish cancelByIdRaw.ops do
    throwError "raw CancelMultipleOrdersById composition is incomplete"
  unless opsHaveIntrinsic (· == .signerKeyN 3) withdrawFundsRaw.ops &&
      opsHaveDataWord 2 1 withdrawFundsRaw.ops &&
      opsHaveUncheckedTransfer 6 4 6 quoteSeeds withdrawFundsRaw.ops &&
      opsHaveUncheckedTransfer 5 3 5 baseSeeds withdrawFundsRaw.ops &&
      opsHaveRawReduceHeader 12 withdrawFundsRaw.ops &&
      opsHaveRawReduceFinish withdrawFundsRaw.ops do
    throwError "raw WithdrawFunds composition is incomplete"
  unless opsHaveIntrinsic (· == .signerKeyN 3) depositFundsRaw.ops &&
      opsHaveDataWord 2 1 depositFundsRaw.ops &&
      opsHaveUnsignedUncheckedTransfer 4 6 2 depositFundsRaw.ops &&
      opsHaveUnsignedUncheckedTransfer 3 5 2 depositFundsRaw.ops &&
      opsHaveRawReduceHeader 13 depositFundsRaw.ops &&
      opsHaveRawReduceFinish depositFundsRaw.ops do
    throwError "raw DepositFunds composition is incomplete"
  let freeTrace := cancelTraceOps cancelAllFreeRaw.ops
  unless traceBefore 1 2 freeTrace && traceBefore 2 3 freeTrace &&
      traceBefore 3 4 freeTrace && traceBefore 4 5 freeTrace &&
      traceBefore 5 6 freeTrace && traceBefore 6 13 freeTrace &&
      traceBefore 13 14 freeTrace do
    throwError s!"CancelAllOrdersWithFreeFunds order changed: {repr freeTrace}"
  let withdrawTrace := cancelTraceOps cancelAllRaw.ops
  unless traceBefore 1 2 withdrawTrace && traceBefore 2 3 withdrawTrace &&
      traceBefore 3 4 withdrawTrace && traceBefore 4 5 withdrawTrace &&
      traceBefore 5 6 withdrawTrace && traceBefore 6 7 withdrawTrace &&
      traceBefore 7 8 withdrawTrace && traceBefore 8 10 withdrawTrace &&
      traceBefore 10 11 withdrawTrace && traceBefore 11 12 withdrawTrace &&
      traceBefore 12 15 withdrawTrace && traceBefore 15 13 withdrawTrace &&
      traceBefore 13 14 withdrawTrace do
    throwError s!"CancelAllOrders query/claim/withdraw order changed: {repr withdrawTrace}"
  match ProofForge.Svm.IR.rawSelfEntry? program with
  | .ok (some entry) =>
      unless entry.tag == 15 && entry.authoritySeed == "log" do
        throwError s!"wrong Phoenix-v1 raw log entry: {repr entry}"
  | result => throwError s!"Phoenix-v1 raw log entry is missing: {repr result}"
  let hasOneBasedRead (word stride capacity : Nat) (ops : Array ProofForge.Svm.IR.Op) :=
    opsHaveAccountQuery (fun
      | .readWord field =>
          field.region.account == 1 && field.firstWord == word &&
            field.region.strideWords == stride && field.region.capacity == capacity &&
            field.region.indexBase == .one
      | _ => false) ops
  unless opsHaveDataWord 1 0 profile.ops && opsHaveDataWord 1 2 profile.ops &&
      opsHaveDataWord 1 3 profile.ops && opsHaveDataWord 1 4 profile.ops &&
      opsHaveDataWord 1 4 seats.ops && opsHaveDataWord 1 34 sequence.ops &&
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
      countDataWordSetAt removeAsk.ops == 0 &&
      opsHaveRbTreeKey4 8314 8315 8316 128 findTrader.ops &&
      opsHaveAccountQuery (fun
        | .key4Find 8310 tree =>
            tree.links.region.account == 1 && tree.links.firstWord == 8314 &&
              tree.parentColor.firstWord == 8315 && tree.key.firstWord == 8316 &&
              tree.links.region.strideWords == 18 && tree.links.region.capacity == 128
        | _ => false) findTrader.ops &&
      opsHaveRbTree 114 115 116 117 512 true findBid.ops &&
      opsHaveAccountQuery (fun
        | .fifoFind 110 tree =>
            tree.links.region.account == 1 && tree.links.firstWord == 114 &&
              tree.parentColor.firstWord == 115 && tree.price.firstWord == 116 &&
              tree.sequence.firstWord == 117 && tree.links.region.strideWords == 8 &&
              tree.links.region.capacity == 512 && tree.bid
        | _ => false) findBid.ops &&
      opsHaveRbTree 4214 4215 4216 4217 512 false findAsk.ops &&
      opsHaveAccountQuery (fun
        | .fifoFind 4210 tree =>
            tree.links.region.account == 1 && tree.links.firstWord == 4214 &&
              tree.parentColor.firstWord == 4215 && tree.price.firstWord == 4216 &&
              tree.sequence.firstWord == 4217 && tree.links.region.strideWords == 8 &&
              tree.links.region.capacity == 512 && !tree.bid
        | _ => false) findAsk.ops &&
      opsHaveRbTreeKey4 8314 8315 8316 128 reduceAsk.ops &&
      opsHaveRbTree 4214 4215 4216 4217 512 false reduceAsk.ops &&
      opsHaveAccountQuery (fun
        | .key4Find 8310 tree => tree.links.region.account == 1
        | _ => false) reduceAsk.ops &&
      opsHaveAccountQuery (fun
        | .fifoFind 4210 tree => !tree.bid
        | _ => false) reduceAsk.ops &&
      hasOneBasedRead 4218 8 512 reduceAsk.ops &&
      hasOneBasedRead 4219 8 512 reduceAsk.ops &&
      hasOneBasedRead 8322 18 128 reduceAsk.ops &&
      hasOneBasedRead 8323 18 128 reduceAsk.ops &&
      opsHaveRbTreeOrderRemove 1 4210 4214 4215 4216 4217 8 512 false reduceAsk.ops &&
      opsHaveOneBasedDataWordSetAt 1 4219 8 512 reduceAsk.ops &&
      opsHaveOneBasedDataWordSetAt 1 8322 18 128 reduceAsk.ops &&
      opsHaveOneBasedDataWordSetAt 1 8323 18 128 reduceAsk.ops &&
      countDataWordSetAt reduceAsk.ops == 5 &&
      opsHaveRbTreeKey4 8314 8315 8316 128 reduceBid.ops &&
      opsHaveRbTree 114 115 116 117 512 true reduceBid.ops &&
      opsHaveDataWord 1 104 reduceBid.ops && opsHaveDataWord 1 105 reduceBid.ops &&
      opsHaveAccountQuery (fun
        | .key4Find 8310 tree => tree.links.region.account == 1
        | _ => false) reduceBid.ops &&
      opsHaveAccountQuery (fun
        | .fifoFind 110 tree => tree.bid
        | _ => false) reduceBid.ops &&
      hasOneBasedRead 118 8 512 reduceBid.ops &&
      hasOneBasedRead 119 8 512 reduceBid.ops &&
      hasOneBasedRead 8320 18 128 reduceBid.ops &&
      hasOneBasedRead 8321 18 128 reduceBid.ops &&
      opsHaveRbTreeOrderRemove 1 110 114 115 116 117 8 512 true reduceBid.ops &&
      opsHaveOneBasedDataWordSetAt 1 119 8 512 reduceBid.ops &&
      opsHaveOneBasedDataWordSetAt 1 8320 18 128 reduceBid.ops &&
      opsHaveOneBasedDataWordSetAt 1 8321 18 128 reduceBid.ops &&
      countDataWordSetAt reduceBid.ops == 5 do
    throwError "Phoenix-v1 profile/body header reads are incomplete"
  unless opsHaveRbTree 114 115 116 117 512 true cursorBid.ops &&
      opsHaveAccountQuery (fun
        | .fifoCursor 110 tree =>
            tree.links.region.account == 1 && tree.links.firstWord == 114 &&
              tree.parentColor.firstWord == 115 && tree.price.firstWord == 116 &&
              tree.sequence.firstWord == 117 && tree.links.region.strideWords == 8 &&
              tree.links.region.capacity == 512 && tree.bid
        | _ => false) cursorBid.ops &&
      opsHaveRbTree 4214 4215 4216 4217 512 false cursorAsk.ops &&
      opsHaveAccountQuery (fun
        | .fifoCursor 4210 tree =>
            tree.links.region.account == 1 && tree.links.firstWord == 4214 &&
              tree.parentColor.firstWord == 4215 && tree.price.firstWord == 4216 &&
              tree.sequence.firstWord == 4217 && tree.links.region.strideWords == 8 &&
              tree.links.region.capacity == 512 && !tree.bid
        | _ => false) cursorAsk.ops do
    throwError "Phoenix-v1 bounded FIFO cursor composition is incomplete"
  let idl := ProofForge.Svm.Idl.emitProgramIdl program
  if idl.contains "\"name\": \"placeLimitOrderWithFreeFunds\"" ||
      idl.contains "\"name\": \"placeLimitOrderWithFreeFundsLimit\"" ||
      idl.contains "\"name\": \"reduceOrderWithFreeFunds\"" ||
      idl.contains "\"name\": \"reduceOrder\"" then
    throwError "raw Phoenix protocol adapter leaked into the generated IDL"
  unless idl.contains
      "\"name\": \"findTrader128\",\n      \"discriminator\": [193, 118, 199, 104, 63, 14, 34, 106],\n      \"accounts\": [{\"name\":\"state\"}, {\"name\":\"acc1\"}]" &&
      idl.contains
      "\"name\": \"findBid512\",\n      \"discriminator\": [245, 172, 68, 54, 84, 34, 9, 191],\n      \"accounts\": [{\"name\":\"state\"}, {\"name\":\"acc1\"}]" &&
      idl.contains
      "\"name\": \"findAsk512\",\n      \"discriminator\": [39, 230, 150, 167, 72, 52, 87, 13],\n      \"accounts\": [{\"name\":\"state\"}, {\"name\":\"acc1\"}]" do
    throwError "bounded find methods must remain read-only in IDL"
  unless idl.contains
      "\"name\": \"cursorBid512\",\n      \"discriminator\": [205, 145, 51, 166, 88, 155, 49, 83],\n      \"accounts\": [{\"name\":\"state\"}, {\"name\":\"acc1\"}]" &&
      idl.contains
      "\"name\": \"cursorAsk512\",\n      \"discriminator\": [35, 69, 96, 252, 35, 19, 247, 46],\n      \"accounts\": [{\"name\":\"state\"}, {\"name\":\"acc1\"}]" do
    throwError "bounded cursor methods must remain read-only in the generated IDL"
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
  unless idl.contains
      "\"name\": \"reduceAskFreeFunds512\",\n      \"discriminator\": [228, 184, 178, 59, 45, 204, 248, 224],\n      \"accounts\": [{\"name\":\"state\",\"writable\":true,\"signer\":true}, {\"name\":\"acc1\",\"writable\":true}]" &&
      idl.contains
      "\"name\": \"reduceBidFreeFunds512\",\n      \"discriminator\": [163, 196, 27, 177, 151, 214, 69, 27],\n      \"accounts\": [{\"name\":\"state\",\"writable\":true,\"signer\":true}, {\"name\":\"acc1\",\"writable\":true}]" do
    throwError "ReduceOrderWithFreeFunds adapters must write the market account"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "jne r2, 40, raw_route_next_" &&
      asm.contains "jne r2, 49, raw_route_next_" &&
      asm.contains "jne r1, 3, raw_route_next_" &&
      asm.contains "jeq r1, 0, raw_route_match_" &&
      asm.contains "jeq r1, 1, raw_route_match_" &&
      asm.contains "jne r2, 26, raw_route_next_" &&
      asm.contains "jeq r1, 4, raw_route_match_" &&
      asm.contains "jeq r1, 5, raw_route_match_" &&
      asm.contains "jne r2, 1, raw_route_next_" &&
      asm.contains "jeq r1, 6, raw_route_match_" &&
      asm.contains "jeq r1, 7, raw_route_match_" &&
      asm.contains "jlt r2, 5, raw_route_next_" &&
      asm.contains "jgt r2, 21, raw_route_next_" &&
      asm.contains "jeq r1, 8, raw_route_match_" &&
      asm.contains "jeq r1, 9, raw_route_match_" &&
      asm.contains "jgt r2, 141, raw_route_next_" &&
      asm.contains "jgt r2, 141, raw_route_next_" &&
      asm.contains "jeq r1, 10, raw_route_match_" &&
      asm.contains "jeq r1, 11, raw_route_match_" &&
      asm.contains "jne r2, 17, raw_route_next_" &&
      asm.contains "jeq r1, 12, raw_route_match_" &&
      asm.contains "jne r2, 17, raw_route_next_" &&
      asm.contains "jeq r1, 13, raw_route_match_" &&
      asm.contains "jlt r2, 1, raw_route_next_" &&
      asm.contains "jeq r1, 15, raw_route_match_" &&
      asm.contains "; checkPdaSeeds account=0 count=1" &&
      asm.contains "; checkPdaSeeds account=3 count=3" &&
      asm.contains "; ownerIsSelf acc=4" &&
      asm.contains "fixed-stride external account word write acc=2 base=34 stride=1 capacity=1" &&
      asm.contains "fixed-stride external account word write acc=2 base=106 stride=1 capacity=1" &&
      asm.contains "bounded one-based acc2 RB find root=110 links=114 stride=8 capacity=512" &&
      asm.contains "bounded one-based acc2 RB find root=4210 links=4214 stride=8 capacity=512" &&
      asm.contains
        "bounded key-based acc2 FIFO cursor root=110 links=114 stride=8 capacity=512" &&
      asm.contains
        "bounded key-based acc2 FIFO cursor root=4210 links=4214 stride=8 capacity=512" &&
      asm.contains "stxdw [r10 - 2248], r1" &&
      asm.contains "jge r1, 65535, fifo_cancel_failure_" &&
      asm.contains "official Solana downward bump allocation bytes=1246 align=8" &&
      asm.contains "jge r1, 32, recorder_append_flush_" &&
      asm.contains "jgt r1, 1246, recorder_append_flush_" &&
      asm.contains "dynamic signed self CPI account=1 data<=1246" &&
      asm.contains "; invoke programIx=8 metas=3 dataLen=9" &&
      asm.contains "signer_seed_data_ok_" do
    throwError "raw Phoenix reduce/cancel adapter and component composition is incomplete"
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
      asm.contains "add64 r9, -3048" &&
      asm.contains "fixed-stride external account word write acc=1 base=8314 stride=18 capacity=128" &&
      asm.contains "fixed-stride external account word write acc=1 base=8315 stride=18 capacity=128" &&
      asm.contains "fixed-stride external account word write acc=1 base=8331 stride=18 capacity=128" &&
      asm.contains "fixed-stride external account word write acc=1 base=8310 stride=1 capacity=1" &&
      asm.contains "ownerIsSelf acc=1" && asm.contains "dws_failure_" &&
      asm.contains "bounded account-resident four-word-key RB insertion" &&
      asm.contains "root=8310 links=8314 parent=8315 key4=8316 stride=18 capacity=128" &&
      asm.contains "function_rb4i_" && asm.contains "_rotate_left" &&
      asm.contains "_rotate_right" &&
      asm.contains "bounded account-resident four-word-key checked add RB insertion" &&
      asm.contains "function_rbtd_" &&
      asm.contains "Existing key4 record: validate both additions before mutating either value" &&
      asm.contains "ldxdw r1, [r8 + 40]" && asm.contains "ldxdw r1, [r8 + 56]" &&
      asm.contains "jlt r3, r1, rbtd_" && asm.contains "stxdw [r10 - 56], r3" &&
      asm.contains "stxdw [r10 - 64], r3" &&
      asm.contains "bounded account-resident four-word-key RB removal" &&
      asm.contains "function_rb4r_" && asm.contains "_transplant" &&
      asm.contains "bounded account-resident descending two-word entry RB insertion" &&
      asm.contains "root=110 links=114 parent=115 key=116 stride=8 capacity=512" &&
      asm.contains "bounded account-resident ascending two-word entry RB insertion" &&
      asm.contains "root=4210 links=4214 parent=4215 key=4216 stride=8 capacity=512" &&
      asm.contains "Sokoban map semantics replace only the existing resting-order value" &&
      asm.contains "stxdw [r8 + 16], r1" && asm.contains "stxdw [r8 + 40], r1" &&
      asm.contains "rsh64 r1, 63" && asm.contains "jne r1, 1" && asm.contains "jne r1, 0" &&
      asm.contains "function_rboi_" &&
      asm.contains "bounded account-resident descending two-word entry RB removal" &&
      asm.contains "bounded account-resident ascending two-word entry RB removal" &&
      asm.contains "function_rbor_" && asm.contains "_transplant" &&
      asm.contains "bounded one-based acc1 RB find root=8310 links=8314 stride=18 capacity=128" &&
      asm.contains "bounded one-based acc1 RB find root=110 links=114 stride=8 capacity=512" &&
      asm.contains "bounded one-based acc1 RB find root=4210 links=4214 stride=8 capacity=512" &&
      asm.contains "bounded key-based acc1 FIFO cursor root=110 links=114 stride=8 capacity=512" &&
      asm.contains "bounded key-based acc1 FIFO cursor root=4210 links=4214 stride=8 capacity=512" &&
      asm.contains "rb_find_found_" && asm.contains "rb_find_missing_" do
    throwError "Phoenix-v1 account data bounds gate is missing"


-- svm-app-002: matching / fee / remainder policy pins (pure arithmetic + entry surface)
#guard takerFeeQuoteLotsOf 0 5 1 == 0
#guard takerFeeQuoteLotsOf 10000 0 1 == 0
#guard takerFeeQuoteLotsOf 10000 5 1 == 5
#guard takerFeeQuoteLotsOf 1 1 1 == 1
#guard takerFeeQuoteLotsOf 9999 1 1 == 1
#guard takerFeeQuoteLotsOf 10000 1 1 == 1
#guard postingQuoteLotsOrZero512At 0 1 10 1 == 0
#guard postingQuoteLotsOrZero512At 100 1 10 1 == 1000
#guard postingQuoteLotsOrZero512At 100 1 10 0 == 0
#guard postingQuoteLotsOrZero512At 100 1 1 3 == 33

#pf_guard_phoenix_v1_profile

end Tests.PhoenixV1ProfileSpec
