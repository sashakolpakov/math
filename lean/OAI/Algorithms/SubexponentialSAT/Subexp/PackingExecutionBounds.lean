import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingGeneratedBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingTailBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketBounds

namespace OAI.Algorithms

/-!
# A fixed polynomial for the complete packing program

The input size includes the actual scope, row and alphabet bytes and the
number of represented types. Every generated tape length is derived below;
no runtime or generated-output bound is supplied by the caller.
-/

namespace SubexponentialSAT.Subexp.PackingExecutionBounds

open BitProgram PackingExecution

variable {U : Type*} [DecidableEq U]

theorem keys_count (s : Spec U) : (keys s).length = s.types.values.length := by simp [keys]

theorem keys_word_le (s : Spec U) :
    ∀ key ∈ keys s, key.length ≤ sourceSize s ^ 2 := by
  intro key hk
  apply type_word_le s key
  rw [s.type_records]
  exact hk

theorem record_bytes_le (s : Spec U) :
    (BucketProgram.encodeRecords (records s)).length ≤ 21000 * sourceSize s ^ 7 := by
  have h := label_stream_le s
  rw [input_labels s, PackingBucketTable.encodeRecords_length_reverse] at h
  exact h

theorem table_payload_le (s : Spec U) :
    ∀ payload ∈ PackingBucketTable.table (records s) (keys s),
      payload.length ≤ 21003 * sourceSize s ^ 7 := by
  intro payload hp
  exact (PackingBucketTable.table_payload_bound (records s) (keys s) (sourceSize s ^ 2)
    (keys_word_le s) payload hp).trans
      (PackingBudgetArithmetic.bucket_payload_le _ _ (sourceSize_pos s) (record_bytes_le s))

theorem table_bytes_le (s : Spec U) :
    (ProgramEncoding.encodeRecords (PackingBucketTable.table (records s) (keys s))).length ≤
      43000 * sourceSize s ^ 8 := by
  have h := PackingBucketTable.table_encoded_bound (records s) (keys s) (sourceSize s ^ 2)
    (keys_word_le s)
  rw [keys_count] at h
  exact h.trans (PackingBudgetArithmetic.bucket_table_le _ _ _ (sourceSize_pos s)
    (count_le s) (record_bytes_le s))

theorem bucket_core_le (s : Spec U) :
    PackingBucketTable.budget (records s) (keys s) ≤ 4400000 * sourceSize s ^ 10 := by
  have h := PackingBucketTable.budget_bound (records s) (keys s) (sourceSize s ^ 2)
    (keys_word_le s)
  rw [keys_count] at h
  exact h.trans (PackingBudgetArithmetic.bucket_core_le _ _ _ (sourceSize_pos s)
    (count_le s) (record_bytes_le s))

theorem block_count_le (s : Spec U) : s.packing.blockCount ≤ s.params.D := by
  rw [← minimum_eq s]
  exact PackingBucketTable.minimum_le _ _ _

theorem buckets_budget_le (s : Spec U) :
    PackingProgram.bucketsBudget (records s) (keys s) s.params.D ≤ 5000000 * sourceSize s ^ 10 := by
  unfold PackingProgram.bucketsBudget
  rw [PackingBucketTable.encodeRecords_length_reverse, ← input_types s]
  exact PackingBudgetArithmetic.bucket_stage_le _ _ _ _ _ _ _ (sourceSize_pos s)
    (record_bytes_le s) (type_stream_le s) (dimension_le s) (table_bytes_le s)
    ((PackingBucketTable.minimum_le _ _ _).trans (dimension_le s)) (bucket_core_le s)

theorem entries_count (s : Spec U) : (entries s).length = s.types.values.length := by
  simp [entries, PackingExtraction.typedEntries, Spec.packing]

theorem entries_word_le (s : Spec U) :
    ∀ entry ∈ entries s, (PackingExtraction.entryWord entry).length ≤ 21003 * sourceSize s ^ 7 := by
  intro entry he
  apply table_payload_le s
  rw [table_eq s]
  exact List.mem_map.mpr ⟨entry, he, rfl⟩

theorem entries_bytes_le (s : Spec U) :
    (ProgramEncoding.encodeRecords ((entries s).map PackingExtraction.entryWord)).length ≤
      43000 * sourceSize s ^ 8 := by
  rw [← table_eq s]
  exact table_bytes_le s

theorem metadata_bytes_le (s : Spec U) : (context s).metadata.length ≤ 34 * sourceSize s ^ 4 := by
  exact (PackingTailBounds.context_metadata_length_le s).trans
    (PackingBudgetArithmetic.metadata_le _ _ _ (sourceSize_pos s) (dimension_le s) (type_stream_le s))

theorem extraction_loop_le (s : Spec U) :
    PackingExtraction.loopBudget (entries s) s.packing.blockCount 0
      (PackingProgram.initialExtraction (entries s) s.packing.blockCount) ≤
        2700000 * sourceSize s ^ 9 := by
  have hn : s.packing.blockCount ≤ sourceSize s := (block_count_le s).trans (dimension_le s)
  have hN : (entries s).length ≤ sourceSize s := by rw [entries_count]; exact count_le s
  have hprod : s.packing.blockCount * (entries s).length ≤ sourceSize s ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hn hN
  have h := PackingExtraction.loopBudget_le (entries s) s.packing.blockCount 0
    (PackingProgram.initialExtraction (entries s) s.packing.blockCount)
    (21003 * sourceSize s ^ 7) (sourceSize s) (sourceSize s ^ 2) (entries_word_le s)
    (by simpa [PackingProgram.initialExtraction] using hn)
    (by simpa [PackingProgram.initialExtraction] using hprod)
  apply h.trans
  exact PackingBudgetArithmetic.extraction_loop_le _ _ _ _ _ (sourceSize_pos s) hn hN
    (entries_bytes_le s) le_rfl

theorem extraction_budget_le (s : Spec U) :
    PackingProgram.extractionBudget (entries s) s.packing.blockCount ≤ 2800000 * sourceSize s ^ 9 := by
  exact PackingBudgetArithmetic.extraction_stage_le _ _ _ _ _ (sourceSize_pos s)
    (extraction_loop_le s) ((block_count_le s).trans (dimension_le s))
    (entries_bytes_le s) (metadata_bytes_le s)

theorem vertices_budget_le (s : Spec U) :
    PackingProgram.verticesBudget s.params.D ≤ 400 * sourceSize s ^ 2 := by
  have hb : s.params.D + 1 ≤ 2 * sourceSize s := by
    have := dimension_le s
    have := sourceSize_pos s
    omega
  apply (PackingProgram.verticesBudget_le s.params.D).trans
  calc
    _ ≤ 100 * (2 * sourceSize s) ^ 2 := by gcongr
    _ = _ := by ring

theorem tail_budget_le (s : Spec U) :
    PackingProgram.leftoversBudget (covered s) s.params.D (context s) +
      PackingProgram.inverseBudget (addressRecords s) s.params.D ≤ 72030000 * sourceSize s ^ 12 :=
  (PackingTailBounds.tail_budget_le s).trans
    (PackingBudgetArithmetic.tail_le _ _ _ (sourceSize_pos s) (dimension_le s) (type_stream_le s))

/-- One coefficient and one degree apply to all represented input types,
dimensions, block counts, row widths and initial alphabets. -/
theorem budget_le (s : Spec U) : PackingExecution.budget s ≤ 81000000 * sourceSize s ^ 12 := by
  have h := PackingBudgetArithmetic.final_le _ _ _ _ _ _ (sourceSize_pos s)
    (frontend_bound_le s) (buckets_budget_le s) (extraction_budget_le s)
    (vertices_budget_le s) (tail_budget_le s)
  unfold PackingExecution.budget
  omega

/-- Actual execution of the complete fixed packing instruction table. -/
theorem program_trace_polynomial (s : Spec U) (regs : Fin 16 → Bool) :
    ∃ steps ≤ 81000000 * sourceSize s ^ 12, ∃ rf,
      Trace PackingProgram.program steps
        ((PackingProgram.inputState s.params.input regs).withPC (some PackingProgram.program.entry))
        ((s.outputState rf).withPC none) := by
  obtain ⟨steps, hs, rf, ht⟩ := PackingExecution.program_trace s regs
  exact ⟨steps, hs.trans (budget_le s), rf, ht⟩

theorem program_primitive_polynomial (s : Spec U) (regs : Fin 16 → Bool) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive PackingProgram.program).step
      (BitProgram.primitiveOverhead PackingProgram.program * (81000000 * sourceSize s ^ 12))
      (BitProgram.primitiveCfg PackingProgram.program
        ((PackingProgram.inputState s.params.input regs).withPC (some PackingProgram.program.entry)))
      (BitProgram.primitiveCfg PackingProgram.program ((s.outputState rf).withPC none)) := by
  obtain ⟨steps, hs, rf, ht⟩ := program_trace_polynomial s regs
  exact ⟨rf, BitProgram.primitive_execution PackingProgram.program ⟨steps, hs, ht⟩⟩

end SubexponentialSAT.Subexp.PackingExecutionBounds

#print axioms SubexponentialSAT.Subexp.PackingExecutionBounds.budget_le
#print axioms SubexponentialSAT.Subexp.PackingExecutionBounds.program_trace_polynomial
#print axioms SubexponentialSAT.Subexp.PackingExecutionBounds.program_primitive_polynomial

end OAI.Algorithms
