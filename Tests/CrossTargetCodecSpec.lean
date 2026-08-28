import ProofForge.Core.Codec
import ProofForge.Evm.Codec
import ProofForge.Svm.EntryAdapter

namespace Tests.CrossTargetCodecSpec

open ProofForge.Core.Codec

private def staticRequest : Schema :=
  .record "Request" #[
    ("amount", .scalar .uint64),
    ("pair", .tuple #[.scalar .uint32, .scalar .boolean]),
    ("levels", .fixedArray 2 (.scalar .uint16))
  ]

-- Both targets retain the same logical source projections while independently choosing Borsh
-- byte widths and ABI words.
#guard
  match ProofForge.Svm.EntryAdapter.borshPlan staticRequest,
      ProofForge.Evm.Codec.inputPlan staticRequest with
  | .ok svm, .ok evm =>
      svm.projections.map (·.sourceName) == evm.projections.map (·.sourceName) &&
      svm.projections.map (·.sourceName) ==
        #["amount", "pair_fst", "pair_snd", "levels_0", "levels_1"] &&
      svm.localWidths == #[8, 4, 1, 2, 2] && svm.minBytes == 17 && svm.maxBytes == 17 &&
      evm.words == #[.uint64, .uint32, .boolean, .uint16, .uint16] &&
      evm.typeName == "(uint64,(uint32,bool),uint16[2])" &&
      evm.headWordCount == 5
  | _, _ => false

private def optionalRequest : Schema :=
  .option (.tuple #[.scalar .uint64, .scalar .boolean])

-- The logical tag/payload frame agrees, but SVM owns variable Borsh bytes while EVM owns
-- fixed Tagged Tuple v1 inactive-zero guards.
#guard
  match ProofForge.Svm.EntryAdapter.borshPlan optionalRequest,
      ProofForge.Evm.Codec.inputPlan optionalRequest with
  | .ok svm, .ok evm =>
      match evm.taggedGuards[0]? with
      | some guard =>
          svm.projections.map (·.sourceName) == evm.projections.map (·.sourceName) &&
          svm.projections.map (·.sourceName) == #["slot_tag", "slot_p0_fst", "slot_p0_snd"] &&
          svm.localWidths == #[1, 8, 1] && svm.minBytes == 1 && svm.maxBytes == 10 &&
          evm.words == #[.boolean, .uint64, .boolean] &&
          evm.typeName == "(bool,(uint64,bool))" &&
          guard.tagWord == 0 && guard.payloadStart == 1 && guard.payloadWords == 2 &&
          guard.activePayloadWords == #[0, 2]
      | none => false
  | _, _ => false

private def boundedItems : Schema :=
  .boundedArray 2 (.record "Item" #[
    ("id", .scalar .uint32),
    ("enabled", .scalar .boolean)
  ])

-- One bounded source frame maps to an exact active-prefix Borsh decoder and a canonical ABI
-- dynamic tail. Capacity remains target plan metadata and no runtime collection is materialized.
#guard
  match ProofForge.Svm.EntryAdapter.borshPlan boundedItems,
      ProofForge.Evm.Codec.inputPlan boundedItems with
  | .ok svm, .ok evm =>
      match evm.boundedArray with
      | some array =>
          svm.projections.map (·.sourceName) == evm.projections.map (·.sourceName) &&
          svm.projections.map (·.sourceName) ==
            #["length", "values_0_id", "values_0_enabled", "values_1_id", "values_1_enabled"] &&
          svm.localWidths == #[4, 4, 1, 4, 1] &&
          svm.localBooleans == #[false, false, true, false, true] &&
          svm.minBytes == 4 && svm.maxBytes == 14 &&
          evm.words == #[.uint32, .uint32, .boolean, .uint32, .boolean] &&
          evm.typeName == "(uint32,bool)[]" && evm.headWordCount == 1 &&
          array.capacity == 2 && array.elementWords == #[.uint32, .boolean]
      | none => false
  | _, _ => false

end Tests.CrossTargetCodecSpec
