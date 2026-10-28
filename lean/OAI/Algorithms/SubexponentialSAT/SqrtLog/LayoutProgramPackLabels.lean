import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExecution

namespace OAI.Algorithms

/-! Packing from physically produced label records. This route accepts the
incidence pair-gatherer's type labels directly, avoiding reconstruction of a
factor-to-incidence scope table. The fixed program computes blocks, uncovered
coordinates, metadata, storage order, and inverse addresses. It does not
assume any of those outputs. Label and universal-type byte production remain
explicit upstream obligations. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

structure Spec (U : Type*) [DecidableEq U] where
  params : PackingFrontend.Params
  types : FiniteEnumeration U
  label : Fin params.D → U
  encodeType : U → List Bool
  encodeType_injective : Function.Injective encodeType

namespace Spec

variable {U : Type*} [DecidableEq U]

/-- The packing algorithm is the existing executable bucket/minimum/index
construction applied only to the represented input labels and type list. -/
def packing (s : Spec U) : PackingData (Fin s.params.D) U :=
  ⟨⟨List.finRange s.params.D, List.nodup_finRange _, List.mem_finRange⟩, s.types, s.label⟩

def encodeVertex (s : Spec U) (v : Fin s.params.D) : List Bool := List.replicate v.val true

def metadata (s : Spec U) : List Bool :=
  SelectorProgram.rawRecords (PackingMetadata.records s.packing s.encodeVertex s.encodeType)

def addresses (s : Spec U) : List Bool :=
  SelectorProgram.rawRecords (PackingAddressSemantics.addressRows
    ((PackingReorder.storageVertices s.packing).map s.encodeVertex) 0).reverse

def storage (s : Spec U) : List Bool :=
  ProgramEncoding.encodeRecords ((PackingReorder.storageVertices s.packing).map s.encodeVertex)

def inverse (s : Spec U) : List Bool :=
  ProgramEncoding.encodeRecords ((PackingReorder.readPlan s.packing).map PackingMetadata.unary)

def outputState (s : Spec U) (regs : Fin 16 → Bool) : PackingProgramSupport.Data :=
  PackingProgram.outputState s.params.input
    (List.replicate s.packing.blockCount true) (List.replicate s.packing.leftovers.length true)
    s.metadata s.addresses s.storage s.inverse regs

@[simp] theorem packing_vertices (s : Spec U) : s.packing.vertices.values = List.finRange s.params.D := rfl
@[simp] theorem packing_label (s : Spec U) : s.packing.label = s.label := rfl
@[simp] theorem packing_types (s : Spec U) : s.packing.types = s.types := rfl

theorem encodeVertex_injective (s : Spec U) : Function.Injective s.encodeVertex := by
  intro v w h
  apply Fin.ext
  have hl := congrArg List.length h
  simpa [encodeVertex] using hl

end Spec

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
  rw [PackingProgram.inverseRows, addressRecords, hq, h]
  simp [PackingMetadata.unary]


abbrev command : Cmd 16 48 :=
  .seq PackingProgram.buckets (.seq PackingProgram.extraction
    (.seq PackingProgram.vertices (.seq PackingProgram.leftovers
      (.seq PackingProgram.inverse (.base .skip)))))
def program := compiled command 26 32

def budget (s : Spec U) : ℕ :=
  PackingProgram.bucketsBudget (records s) (keys s) s.params.D +
  PackingProgram.extractionBudget (entries s) s.packing.blockCount +
  PackingProgram.verticesBudget s.params.D +
  PackingProgram.leftoversBudget (covered s) s.params.D (context s) +
  PackingProgram.inverseBudget (addressRecords s) s.params.D + 1

theorem leftover_outputs (s : Spec U) :
    let result := PackingProgram.leftoverResult (covered s) s.params.D (context s)
    result.metadata = s.metadata ∧ result.addresses = s.addresses ∧
    result.storage.reverse ++ [false] = s.storage ∧ result.rank = s.packing.leftovers.length := by
  have h := PackingOutputSemantics.finish_extraction_outputs s.packing Fin.val s.encodeType
    Fin.val_injective (PackingProgram.initialExtraction (entries s) s.packing.blockCount)
    rfl rfl rfl rfl rfl
  have he : PackingProgram.leftoverResult (covered s) s.params.D (context s) =
      PackingOutputSemantics.finish s.packing Fin.val s.encodeType
        (PackingOutputSemantics.snapshotOf (context s)) := by
    simp only [PackingProgram.leftoverResult, PackingOutputSemantics.finish, Spec.packing,
      List.map_coe_finRange] ; rfl
  change (PackingOutputSemantics.finish s.packing Fin.val s.encodeType
      (PackingOutputSemantics.snapshotOf (context s))).metadata = _ ∧ _ at h
  dsimp only
  simp only [he]
  refine ⟨h.1, h.2.2.1, ?_, h.2.2.2.1⟩
  have hstorage : (PackingOutputSemantics.finish s.packing Fin.val s.encodeType
      (PackingOutputSemantics.snapshotOf (context s))).storage =
      (PackingExtraction.vertexPrefix
        ((PackingReorder.storageVertices s.packing).map s.encodeVertex)).reverse := h.2.1
  rw [hstorage, List.reverse_reverse]
  exact (SelectorMapProgram.encodeRecords_eq_prefix
    ((PackingReorder.storageVertices s.packing).map s.encodeVertex)).symm

/-- Every packing stage after label/type production is a concrete finite program.
Only encoded input labels and the full encoded type alphabet are assumed. -/
theorem program_trace (s : Spec U) (regs : Fin 16 → Bool) :
    ∃ steps ≤ budget s, ∃ rf,
      Trace program steps
        ((PackingProgram.frontendOutputState s.params.input
          (BucketProgram.encodeRecords (records s).reverse)
          (ProgramEncoding.encodeRecords (keys s)) regs).withPC (some program.entry))
        ((s.outputState rf).withPC none) := by
  have hc : s.params.D ≤ (records s).length := by
    simp [records, BucketProgram.vertexRecords, Spec.packing]
  obtain ⟨nb, hnb, rb, hb⟩ := PackingProgram.buckets_eval s.params.input (records s) (keys s)
    s.params.D rfl hc regs
  rw [minimum_eq s, table_eq s] at hb
  obtain ⟨ne, hne, re, he⟩ := PackingProgram.extraction_eval s.params.input (entries s)
    s.packing.blockCount (PackingExtraction.typedEntries_valid s.packing s.encodeVertex s.encodeType) rb
  obtain ⟨nv, hnv, rv, hv⟩ := PackingProgram.vertices_eval s.params.input s.packing.blockCount
    s.params.D (context s) rfl re
  obtain ⟨nl, hnl, rl, hl⟩ := PackingProgram.leftovers_eval s.params.input s.packing.blockCount
    s.params.D (context s) (covered s) (context_metadata s) (context_address s) rv
  obtain ⟨hm, ha, hs, hr⟩ := leftover_outputs s
  rw [hm, ha, hs, hr] at hl
  obtain ⟨ni, hni, ri, hi⟩ := PackingProgram.inverse_eval s.params.input
    (List.replicate s.packing.blockCount true) (List.replicate s.packing.leftovers.length true)
    s.metadata s.storage (addressRecords s) s.params.D rfl rl
  rw [inverse_rows s] at hi
  have hi' : Eval PackingProgram.inverse ni
      (PackingProgram.outputState s.params.input (List.replicate s.packing.blockCount true)
        (List.replicate s.packing.leftovers.length true) s.metadata s.addresses s.storage [] rl)
      (s.outputState ri) := by
    simpa only [Spec.outputState, Spec.addresses, addressRecords,
      PackingAddressSemantics.storageAddresses, Spec.inverse] using hi
  have hpacking := hb.seq (he.seq (hv.seq (hl.seq (hi'.seq (.base (.skip _))))))
  have hall : Eval command (nb + (ne + (nv + (nl + (ni + 0)))))
      (PackingProgram.frontendOutputState s.params.input
        (BucketProgram.encodeRecords (records s).reverse)
        (ProgramEncoding.encodeRecords (keys s)) regs) (s.outputState ri) := hpacking
  refine ⟨nb + (ne + (nv + (nl + (ni + 0)))) + 1, ?_, ri,
    compiled_halt_trace hall 26 32⟩
  unfold budget
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

end OAI.Algorithms
