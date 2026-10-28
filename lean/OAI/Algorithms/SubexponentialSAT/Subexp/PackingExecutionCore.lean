import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExecutionSpec
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionStage
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingInverseStage

namespace OAI.Algorithms

/-! Semantic identifications used by the final physical packing execution. -/
namespace SubexponentialSAT.Subexp.PackingExecution

open BitProgram StructuredCalls

variable {U : Type*} [DecidableEq U]

def records (s : Spec U) : List BucketProgram.Record :=
  BucketProgram.vertexRecords s.packing.vertices.values s.packing.label s.encodeType s.encodeVertex

def keys (s : Spec U) : List (List Bool) := s.types.values.map s.encodeType

def entries (s : Spec U) : List PackingExtraction.Entry :=
  PackingExtraction.typedEntries s.packing s.encodeVertex s.encodeType

def context (s : Spec U) : PackingExtraction.Context :=
  PackingProgram.extracted (entries s) s.packing.blockCount

def covered (s : Spec U) : List (List Bool × List Bool) :=
  PackingMetadata.coveredRecords s.packing s.encodeVertex s.encodeType

def addressRecords (s : Spec U) : List (List Bool × List Bool) :=
  PackingAddressSemantics.storageAddresses s.packing s.encodeVertex

theorem input_labels (s : Spec U) :
    s.params.labelStream = BucketProgram.encodeRecords (records s).reverse := by
  unfold PackingFrontend.Params.labelStream
  rw [s.label_records]
  rfl

theorem input_types (s : Spec U) :
    s.params.typeStream = ProgramEncoding.encodeRecords (keys s) := by
  unfold PackingFrontend.Params.typeStream
  rw [s.type_records]
  rfl

theorem minimum_eq (s : Spec U) :
    PackingBucketTable.minimum (records s) (keys s) s.params.D = s.packing.blockCount := by
  have h := PackingBucketTable.minimum_eq_blockCount s.packing s.encodeType s.encodeVertex
    s.encodeType_injective
  simpa only [records, keys, Spec.packing, List.length_finRange] using h

theorem table_eq (s : Spec U) :
    PackingBucketTable.table (records s) (keys s) = (entries s).map PackingExtraction.entryWord := by
  change PackingBucketTable.table
    (BucketProgram.vertexRecords s.packing.vertices.values s.packing.label s.encodeType s.encodeVertex)
    (s.packing.types.values.map s.encodeType) = _
  rw [PackingBucketTable.table_eq_typed s.packing s.encodeType s.encodeVertex s.encodeType_injective]
  simp only [entries, PackingExtraction.typedEntries, List.map_map,
    PackingExtraction.entryWord, PackingExtraction.bucketWord, Function.comp_def]

theorem context_metadata (s : Spec U) :
    (context s).metadata = SelectorProgram.rawRecords (covered s) := by
  have h := PackingExtraction.typed_extraction_metadata s.packing s.encodeVertex s.encodeType
    (PackingProgram.initialExtraction (entries s) s.packing.blockCount) rfl
  simpa only [context, PackingProgram.extracted, entries, covered,
    PackingProgram.initialExtraction, List.append_nil] using h

theorem context_address (s : Spec U) :
    (context s).address = List.replicate (context s).address.length true := by
  have h := PackingExtraction.advanceMany_address_unary (entries s) s.packing.blockCount 0
    (PackingProgram.initialExtraction (entries s) s.packing.blockCount) 0 rfl
  change (context s).address = _ at h
  rw [h]
  simp [PackingMetadata.unary]

theorem inverse_rows (s : Spec U) :
    PackingProgram.inverseRows (addressRecords s) s.params.D =
      (PackingReorder.readPlan s.packing).map PackingMetadata.unary := by
  have h := PackingAddressSemantics.mappedRecords_eq_readPlan s.packing s.encodeVertex
    s.encodeVertex_injective
  have hq : PackingProgram.inverseQueries s.params.D =
      s.packing.vertices.values.reverse.map s.encodeVertex := by
    simp only [PackingProgram.inverseQueries, Spec.packing,
      ← List.range_eq_range', ← List.map_coe_finRange, List.map_reverse, List.map_map,
      Function.comp_def, PackingMetadata.unary] ; rfl
  change SelectorMapProgram.mappedRecords
    (PackingAddressSemantics.storageAddresses s.packing s.encodeVertex)
    (PackingProgram.inverseQueries s.params.D) = _
  rw [hq]
  change _ = (PackingReorder.readPlan s.packing).map (fun i => List.replicate i true)
  exact h


end SubexponentialSAT.Subexp.PackingExecution

end OAI.Algorithms
