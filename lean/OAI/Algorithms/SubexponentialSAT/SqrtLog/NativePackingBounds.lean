import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NativePackingBoundsGenerated
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NativePackingBoundsTail
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketBounds

namespace OAI.Algorithms

/-! Polynomial cost of the actual native address-plan suffix. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram LayoutProgram
variable {U : Type*} [DecidableEq U]

theorem input_labels (s : NativePacking.Spec U) :
    s.params.labelStream=BucketProgram.encodeRecords (PackLabels.records s.suffix).reverse := by
  rw [NativeFrontend.Params.labelStream,s.label_records]
  rfl

theorem input_types (s : NativePacking.Spec U) :
    s.params.typeStream=ProgramEncoding.encodeRecords (PackLabels.keys s.suffix) := by
  rw [NativeFrontend.Params.typeStream,s.type_records]
  rfl

theorem keys_count (s : NativePacking.Spec U) : (PackLabels.keys s.suffix).length = s.types.values.length := by simp [PackLabels.keys,NativePacking.Spec.suffix]

theorem keys_word_le (s : NativePacking.Spec U) :
    ∀ key ∈ PackLabels.keys s.suffix, key.length ≤ sourceSize s ^ 2 := by
  intro key hk
  apply type_word_le s key
  rw [s.type_records]
  exact hk

theorem record_bytes_le (s : NativePacking.Spec U) :
    (BucketProgram.encodeRecords (PackLabels.records s.suffix)).length ≤ 21000 * sourceSize s ^ 7 := by
  have h := label_stream_le s
  rw [input_labels s, PackingBucketTable.encodeRecords_length_reverse] at h
  exact h

theorem table_payload_le (s : NativePacking.Spec U) :
    ∀ payload ∈ PackingBucketTable.table (PackLabels.records s.suffix) (PackLabels.keys s.suffix),
      payload.length ≤ 21003 * sourceSize s ^ 7 := by
  intro payload hp
  exact (PackingBucketTable.table_payload_bound (PackLabels.records s.suffix) (PackLabels.keys s.suffix) (sourceSize s ^ 2)
    (keys_word_le s) payload hp).trans
      (PackingBudgetArithmetic.bucket_payload_le _ _ (sourceSize_pos s) (record_bytes_le s))

theorem table_bytes_le (s : NativePacking.Spec U) :
    (ProgramEncoding.encodeRecords (PackingBucketTable.table (PackLabels.records s.suffix) (PackLabels.keys s.suffix))).length ≤
      43000 * sourceSize s ^ 8 := by
  have h := PackingBucketTable.table_encoded_bound (PackLabels.records s.suffix) (PackLabels.keys s.suffix) (sourceSize s ^ 2)
    (keys_word_le s)
  rw [keys_count] at h
  exact h.trans (PackingBudgetArithmetic.bucket_table_le _ _ _ (sourceSize_pos s)
    (count_le s) (record_bytes_le s))

theorem bucket_core_le (s : NativePacking.Spec U) :
    PackingBucketTable.budget (PackLabels.records s.suffix) (PackLabels.keys s.suffix) ≤ 4400000 * sourceSize s ^ 10 := by
  have h := PackingBucketTable.budget_bound (PackLabels.records s.suffix) (PackLabels.keys s.suffix) (sourceSize s ^ 2)
    (keys_word_le s)
  rw [keys_count] at h
  exact h.trans (PackingBudgetArithmetic.bucket_core_le _ _ _ (sourceSize_pos s)
    (count_le s) (record_bytes_le s))

theorem block_count_le (s : NativePacking.Spec U) : s.suffix.packing.blockCount ≤ s.params.D := by
  rw [← PackLabels.minimum_eq s.suffix]
  exact PackingBucketTable.minimum_le _ _ _

theorem buckets_budget_le (s : NativePacking.Spec U) :
    PackingProgram.bucketsBudget (PackLabels.records s.suffix) (PackLabels.keys s.suffix) s.params.D ≤ 5000000 * sourceSize s ^ 10 := by
  unfold PackingProgram.bucketsBudget
  rw [PackingBucketTable.encodeRecords_length_reverse, ← input_types s]
  exact PackingBudgetArithmetic.bucket_stage_le _ _ _ _ _ _ _ (sourceSize_pos s)
    (record_bytes_le s) (type_stream_le s) (dimension_le s) (table_bytes_le s)
    ((PackingBucketTable.minimum_le _ _ _).trans (dimension_le s)) (bucket_core_le s)

theorem entries_count (s : NativePacking.Spec U) : (PackLabels.entries s.suffix).length = s.types.values.length := by
  simp [PackLabels.entries, PackingExtraction.typedEntries, PackLabels.Spec.packing, NativePacking.Spec.suffix]

theorem entries_word_le (s : NativePacking.Spec U) :
    ∀ entry ∈ PackLabels.entries s.suffix, (PackingExtraction.entryWord entry).length ≤ 21003 * sourceSize s ^ 7 := by
  intro entry he
  apply table_payload_le s
  rw [PackLabels.table_eq s.suffix]
  exact List.mem_map.mpr ⟨entry, he, rfl⟩

theorem entries_bytes_le (s : NativePacking.Spec U) :
    (ProgramEncoding.encodeRecords ((PackLabels.entries s.suffix).map PackingExtraction.entryWord)).length ≤
      43000 * sourceSize s ^ 8 := by
  rw [← PackLabels.table_eq s.suffix]
  exact table_bytes_le s

theorem metadata_bytes_le (s : NativePacking.Spec U) : (PackLabels.context s.suffix).metadata.length ≤ 34 * sourceSize s ^ 4 := by
  exact (context_metadata_length_le s).trans
    (PackingBudgetArithmetic.metadata_le _ _ _ (sourceSize_pos s) (dimension_le s) (type_stream_le s))

theorem extraction_loop_le (s : NativePacking.Spec U) :
    PackingExtraction.loopBudget (PackLabels.entries s.suffix) s.suffix.packing.blockCount 0
      (PackingProgram.initialExtraction (PackLabels.entries s.suffix) s.suffix.packing.blockCount) ≤
        2700000 * sourceSize s ^ 9 := by
  have hn : s.suffix.packing.blockCount ≤ sourceSize s := (block_count_le s).trans (dimension_le s)
  have hN : (PackLabels.entries s.suffix).length ≤ sourceSize s := by rw [entries_count]; exact count_le s
  have hprod : s.suffix.packing.blockCount * (PackLabels.entries s.suffix).length ≤ sourceSize s ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hn hN
  have h := PackingExtraction.loopBudget_le (PackLabels.entries s.suffix) s.suffix.packing.blockCount 0
    (PackingProgram.initialExtraction (PackLabels.entries s.suffix) s.suffix.packing.blockCount)
    (21003 * sourceSize s ^ 7) (sourceSize s) (sourceSize s ^ 2) (entries_word_le s)
    (by simpa [PackingProgram.initialExtraction] using hn)
    (by simpa [PackingProgram.initialExtraction] using hprod)
  apply h.trans
  exact PackingBudgetArithmetic.extraction_loop_le _ _ _ _ _ (sourceSize_pos s) hn hN
    (entries_bytes_le s) le_rfl

theorem extraction_budget_le (s : NativePacking.Spec U) :
    PackingProgram.extractionBudget (PackLabels.entries s.suffix) s.suffix.packing.blockCount ≤ 2800000 * sourceSize s ^ 9 := by
  exact PackingBudgetArithmetic.extraction_stage_le _ _ _ _ _ (sourceSize_pos s)
    (extraction_loop_le s) ((block_count_le s).trans (dimension_le s))
    (entries_bytes_le s) (metadata_bytes_le s)

theorem vertices_budget_le (s : NativePacking.Spec U) :
    PackingProgram.verticesBudget s.params.D ≤ 400 * sourceSize s ^ 2 := by
  have hb : s.params.D + 1 ≤ 2 * sourceSize s := by
    have := dimension_le s
    have := sourceSize_pos s
    omega
  apply (PackingProgram.verticesBudget_le s.params.D).trans
  calc
    _ ≤ 100 * (2 * sourceSize s) ^ 2 := by gcongr
    _ = _ := by ring

theorem tail_budget_scaled_le (s : NativePacking.Spec U) :
    PackingProgram.leftoversBudget (PackLabels.covered s.suffix) s.params.D (PackLabels.context s.suffix) +
      PackingProgram.inverseBudget (PackLabels.addressRecords s.suffix) s.params.D ≤ 72030000 * sourceSize s ^ 12 :=
  (tail_budget_le s).trans
    (PackingBudgetArithmetic.tail_le _ _ _ (sourceSize_pos s) (dimension_le s) (type_stream_le s))

/-- One coefficient and one degree apply to all represented input types,
dimensions, block counts, row widths and initial alphabets. -/
theorem budget_le (s : NativePacking.Spec U) : NativePacking.budget s ≤ 81000000 * sourceSize s ^ 12 := by
  have h := PackingBudgetArithmetic.final_le _ _ _ _ _ _ (sourceSize_pos s)
    (frontend_bound_le s) (buckets_budget_le s) (extraction_budget_le s)
    (vertices_budget_le s) (tail_budget_scaled_le s)
  unfold NativePacking.budget PackLabels.budget
  have hD : s.suffix.params.D=s.params.D := rfl
  simp only [hD]
  omega

/-- The bound is on the exact suffix called by the concrete packing caller. -/
theorem program_trace_polynomial (s : NativePacking.Spec U) (regs : Fin 16 → Bool) :
    ∃ steps ≤ 81000000*sourceSize s^12, ∃ rf,
      Trace NativePacking.program steps
        ((NativeFrontend.plansState s.params regs).withPC (some NativePacking.program.entry))
        ((s.suffix.outputState rf).withPC none) := by
  obtain ⟨steps,hs,rf,ht⟩ := NativePacking.program_trace s regs
  exact ⟨steps,hs.trans (budget_le s),rf,ht⟩

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
