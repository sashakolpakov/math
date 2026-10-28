import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExecutionCore
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrontend
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingLeftoverStage
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingInverseStage

namespace OAI.Algorithms

/-! Composition of the actual finite programs from assignment bytes through
complete blocks, leftovers, metadata, storage order, and inverse addresses. -/

namespace SubexponentialSAT.Subexp.PackingExecution

open BitProgram StructuredCalls

variable {U : Type*} [DecidableEq U]

def budget (s : Spec U) : ℕ :=
  s.params.bound + PackingProgram.bucketsBudget (records s) (keys s) s.params.D +
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

/-- This theorem executes every stage; it takes no packing-output or subroutine
execution premise. `Spec` carries only independently checkable input encodings. -/
theorem program_trace (s : Spec U) (regs : Fin 16 → Bool) :
    ∃ steps ≤ budget s, ∃ rf,
      Trace PackingProgram.program steps
        ((PackingProgram.inputState s.params.input regs).withPC (some PackingProgram.program.entry))
        ((s.outputState rf).withPC none) := by
  obtain ⟨nf, rf, hnf, hf⟩ := PackingFrontend.frontend_eval s.params regs
    s.degree_bound s.rows_width s.rows_count
  rw [input_labels s, input_types s] at hf
  have hc : s.params.D ≤ (records s).length := by
    simp [records, BucketProgram.vertexRecords, Spec.packing]
  obtain ⟨nb, hnb, rb, hb⟩ := PackingProgram.buckets_eval s.params.input (records s) (keys s)
    s.params.D rfl hc rf
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
  have hall : Eval PackingProgram.command (nf + (nb + (ne + (nv + (nl + (ni + 0))))))
      (PackingProgram.inputState s.params.input regs) (s.outputState ri) := hf.seq hpacking
  refine ⟨nf + (nb + (ne + (nv + (nl + (ni + 0))))) + 1, ?_, ri,
    compiled_halt_trace hall 40 32⟩
  unfold budget
  omega

theorem program_primitive (s : Spec U) (regs : Fin 16 → Bool) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive PackingProgram.program).step
      (BitProgram.primitiveOverhead PackingProgram.program * budget s)
      (BitProgram.primitiveCfg PackingProgram.program
        ((PackingProgram.inputState s.params.input regs).withPC (some PackingProgram.program.entry)))
      (BitProgram.primitiveCfg PackingProgram.program ((s.outputState rf).withPC none)) := by
  obtain ⟨steps, hs, rf, ht⟩ := program_trace s regs
  exact ⟨rf, BitProgram.primitive_execution PackingProgram.program ⟨steps, hs, ht⟩⟩

end SubexponentialSAT.Subexp.PackingExecution

end OAI.Algorithms
