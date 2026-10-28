import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorQueryReplay

/-! Actual factor and source instructions preserve caller bank744–767.
The certificate inspects the 340-stack source embedding and every staging,
cache, dispatch, arithmetic and cleanup command; a generic 768-stack lift
alone does not establish this exclusion. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryFactorKeptFrame.SourceFrames

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

local notation "H" => (fun i : Fin 768 => 744 ≤ Fin.val i ∧ Fin.val i < 768)

theorem low_port (i : Fin 768) (hi : i.val < 744) : ¬ H i := by omega

theorem source_before_avoids : AvoidsCmd H SourceStaging.before := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_, avoids_clearMany _ _ ?_⟩
  · simp [SourceStaging.savePairs]
  · simp [SourceStaging.cachePorts]

theorem source_after_avoids : AvoidsCmd H SourceStaging.after := by
  refine ⟨avoids_clearMany _ _ ?_, avoids_copyMany _ _ _ (by decide) ?_,
    avoids_clearMany _ _ ?_, avoids_clearMany _ _ ?_⟩
  · simp [SourceStaging.cachePorts]
  · simp [SourceStaging.restorePairs]
  · simp [SourceStaging.backupPorts]
  · intro i hi
    obtain ⟨j, _, rfl⟩ := (SourceStaging.lowClear_iff i).mp hi
    exact low_port _ (by change 340 + j.val < 744; omega)

theorem source_prepare_avoids : AvoidsCmd H SourceControls.prepare := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_, True.intro, ?_⟩
  · simp [SourceControls.pairs]
  · change ¬ H 365
    decide

theorem source_cleanup_avoids : AvoidsCmd H SourceControls.cleanup := by
  apply avoids_clearMany
  intro i hi
  have hh := (SourceControls.mem_extraPorts i).mp hi
  exact low_port i (by omega)

theorem source_avoids : AvoidsCmd H Source.command := by
  refine ⟨source_before_avoids, source_prepare_avoids, ?_,
    source_after_avoids, source_cleanup_avoids⟩
  apply avoids_call_lift_of_range
  intro i
  exact low_port _ (by change 340 + i.val < 744; omega)

theorem stage_avoids : AvoidsCmd H Incidence.stage := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_,
    avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide), True.intro, ?_⟩
  · simp [Incidence.pairs]
  · change ¬ H 550
    decide

theorem export_avoids : AvoidsCmd H Incidence.exportResult := by
  refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide),
    avoids_clearMany _ _ ?_⟩
  intro i hi
  exact low_port i (by have hh := (Incidence.mem_workerPorts i).mp hi; omega)

namespace Table
open FactorTableProgram
local notation "HW" => (fun i : Fin 896 => 744 ≤ Fin.val i ∧ Fin.val i < 768)

theorem base_predicate (i : Fin 768) : HW (basePort i) ↔ H i := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem base_avoids (i : Fin 768) (hi : i.val < 744) : ¬ HW (basePort i) := by
  rw [base_predicate]
  omega

theorem lift_base_avoids (c : Cmd 16 768) (hc : AvoidsCmd H c) :
    AvoidsCmd HW (liftBase c) := by
  apply avoids_liftProgram
  have hp : (fun i : Fin 768 => HW (basePort i)) = H := by
    funext i
    exact propext (base_predicate i)
  change AvoidsProgram (fun i : Fin 768 => HW (basePort i)) (compiled c 0 0)
  rw [hp]
  exact avoids_compiled _ _ hc _ _

theorem inner_avoids (c : Cmd 16 256) :
    AvoidsCmd HW (liftInner c) := by
  apply avoids_liftCommand_of_range
  intro i
  change ¬ (744 ≤ 340+i.val ∧ 340+i.val < 768)
  omega

theorem specialize_avoids : AvoidsCmd HW specializeCall := by
  refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide), ?_⟩
  apply avoids_liftCommand_of_range
  intro i
  change ¬ (744 ≤ 340+i.val ∧ 340+i.val < 768)
  omega

theorem low_payload_avoids : AvoidsCmd HW lowPayload :=
  ⟨lift_base_avoids _ source_avoids, specialize_avoids⟩

theorem literal_payload_avoids : AvoidsCmd HW literalPayload :=
  ⟨inner_avoids _, inner_avoids _, low_payload_avoids⟩

theorem literal_iteration_avoids : AvoidsCmd HW literalIteration :=
  ⟨inner_avoids _, literal_payload_avoids, inner_avoids _⟩

theorem prepare_factor_avoids : AvoidsCmd HW prepareFactor :=
  ⟨inner_avoids _, avoids_forCmd _ _ _ (by decide) literal_iteration_avoids,
    inner_avoids _⟩

theorem entry_avoids : AvoidsCmd HW initializeWorker := by
  apply avoids_clearMany
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hj' := (Incidence.mem_workerPorts j).mp (List.mem_filter.mp hj).1
    exact base_avoids j (by omega)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Table

theorem command_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768) FactorTableProgram.command :=
  ⟨Table.entry_avoids, Table.lift_base_avoids _ stage_avoids,
    Table.prepare_factor_avoids, Table.lift_base_avoids _ export_avoids⟩

theorem program_avoids :
    AvoidsProgram (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768) FactorTableProgram.program :=
  avoids_compiled _ _ command_avoids _ _

theorem caller_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768) FactorTableProgram.caller :=
  avoids_liftProgram _ _ _ _ program_avoids

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryFactorKeptFrame.SourceFrames

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryFactorKeptFrame

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

local notation "H" => (fun i : Fin 768 => 744 ≤ Fin.val i ∧ Fin.val i < 768)
local notation "HW" => (fun i : Fin 896 => 744 ≤ Fin.val i ∧ Fin.val i < 768)

private theorem lift_low_avoids (c : Cmd 40 768) (input output : Fin 768)
    (hc : AvoidsCmd H c) :
    AvoidsCmd HW (FactorAssignmentProgram.liftLow c input output) :=
  avoids_liftProgram _ _ _ _ (avoids_compiled H c hc input output)

private theorem cache_local_avoids : AvoidsCmd H LeafNodeCacheProgram.localCommand := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_, ?_,
    avoids_copyMany _ _ _ (by decide) ?_, avoids_clearCmd _ _ (by decide)⟩
  · simp [LeafNodeCacheProgram.copies, LeafNodeCacheProgram.directCopies]
  · apply avoids_call_lift_of_range
    intro i
    change ¬ (744 ≤ 340 + i.val ∧ 340 + i.val < 768)
    omega
  · simp

/-- The actual paid cache constructor excludes every word in bank744–767. -/
theorem setup_avoids : AvoidsCmd HW FactorAssignmentProgram.setup := by
  apply avoids_liftProgram
  exact avoids_compiled H FactorAssignmentProgram.setupLocal
    ⟨avoids_clearMany _ _ (by
      simp [FactorAssignmentProgram.cachePorts, LeafNodeCacheProgram.cachePorts,
        LeafNodeCacheProgram.pocket]), cache_local_avoids⟩ 128 69

private theorem factor_copy_avoids (src dst : Fin 768)
    (hs : ¬ H src) (hd : ¬ H dst) : AvoidsCmd H (Factor.copy src dst) :=
  avoids_copyProgram H src dst 159 0 1 hs hd (by decide)

private theorem factor_clear_avoids (src : Fin 768) (hs : ¬ H src) :
    AvoidsCmd H (Factor.clear src) := avoids_clearProgram H src 0 1 hs

private theorem factor_move_avoids (src dst : Fin 768)
    (hs : ¬ H src) (hd : ¬ H dst) : AvoidsCmd H (Factor.move src dst) :=
  ⟨factor_copy_avoids src dst hs hd, factor_clear_avoids src hs⟩

private theorem multiply_avoids : AvoidsCmd H Factor.multiply := by
  apply avoids_call_lift_of_range
  intro i
  change ¬ (744 ≤ i.val ∧ i.val < 768)
  omega

private theorem accumulate_avoids : AvoidsCmd H Factor.accumulate :=
  ⟨factor_move_avoids _ _ (by decide) (by decide),
    factor_move_avoids _ _ (by decide) (by decide), multiply_avoids,
    factor_move_avoids _ _ (by decide) (by decide)⟩

private theorem indicator_avoids : AvoidsCmd H Factor.indicator := by
  refine ⟨⟨True.intro, True.intro, True.intro⟩, ?_⟩
  apply avoids_call_lift_of_range
  decide

private theorem clause_avoids : AvoidsCmd H Clause.caller := by
  apply avoids_call_lift_of_range
  intro i
  change ¬ (744 ≤ i.val ∧ i.val < 768)
  omega

theorem hash_arithmetic_avoids : AvoidsCmd H FactorEvaluationSpace.hashArithmetic :=
  ⟨indicator_avoids, factor_clear_avoids _ (by decide),
    factor_clear_avoids _ (by decide), accumulate_avoids⟩

theorem marked_arithmetic_avoids : AvoidsCmd H FactorEvaluationSpace.markedArithmetic :=
  ⟨clause_avoids, factor_clear_avoids _ (by decide), accumulate_avoids⟩

private theorem expansion_avoids : AvoidsCmd H Expansion.forwardCommand := by
  constructor
  · intro q
    fin_cases q <;> simp [AvoidsInstr]
  · apply avoids_call_lift_of_range
    decide

private theorem factor_id_avoids : AvoidsCmd H FactorID.command :=
  ⟨avoids_copyProgram H 149 556 359 0 1 (by decide) (by decide) (by decide),
    by change ¬ H 556; decide⟩

private theorem dispatcher_avoids : AvoidsCmd H FactorDispatch.command := by
  refine ⟨⟨avoids_copyProgram H 149 152 359 0 1 (by decide) (by decide) (by decide),
    (by change ¬ H 706; decide)⟩, ?_⟩
  apply avoids_call_lift_of_range
  decide

private theorem callback_scratch_avoids :
    ∀ i ∈ FactorAssignmentProgram.callbackScratch, ¬ H i := by
  simp [FactorAssignmentProgram.callbackScratch, FactorServices.indicatorScratch,
    Factor.indicatorStacks, Factor.nativeStacks, FactorDispatch.scratch, Expansion.scratch,
    Equiv.swap_apply_def]

private theorem clear_callback_avoids : AvoidsCmd HW FactorAssignmentProgram.clearCallback := by
  apply avoids_liftProgram
  exact avoids_compiled H FactorAssignmentProgram.clearCallbackLocal
    (avoids_clearMany H _ callback_scratch_avoids) 149 149

theorem prepare_incidence_avoids :
    AvoidsCmd HW FactorAssignmentProgram.prepareIncidence :=
  ⟨lift_low_avoids _ _ _ factor_id_avoids, SourceFrames.caller_avoids⟩

private theorem choose_avoids : AvoidsCmd HW FactorAssignmentProgram.choose :=
  ⟨⟨prepare_incidence_avoids,
      lift_low_avoids _ _ _ ⟨expansion_avoids, hash_arithmetic_avoids⟩⟩,
    ⟨prepare_incidence_avoids,
      lift_low_avoids _ _ _
        ⟨factor_move_avoids _ _ (by decide) (by decide), marked_arithmetic_avoids⟩⟩,
    True.intro⟩

private theorem copy_avoids (src dst : Fin 896)
    (hs : ¬ HW src) (hd : ¬ HW dst) :
    AvoidsCmd HW (FactorAssignmentProgram.copy src dst) :=
  avoids_copyProgram HW src dst 159 0 1 hs hd (by decide)

private theorem clear_avoids (src : Fin 896) (hs : ¬ HW src) :
    AvoidsCmd HW (FactorAssignmentProgram.clear src) := avoids_clearProgram HW src 0 1 hs

private theorem move_avoids (src dst : Fin 896)
    (hs : ¬ HW src) (hd : ¬ HW dst) :
    AvoidsCmd HW (FactorAssignmentProgram.move src dst) :=
  ⟨copy_avoids src dst hs hd, clear_avoids src hs⟩

theorem hash_factor_avoids : AvoidsCmd HW FactorAssignmentProgram.hashFactor :=
  ⟨prepare_incidence_avoids, lift_low_avoids _ _ _ ⟨expansion_avoids, hash_arithmetic_avoids⟩⟩

theorem marked_factor_avoids : AvoidsCmd HW FactorAssignmentProgram.markedFactor :=
  ⟨prepare_incidence_avoids, lift_low_avoids _ _ _
    ⟨factor_move_avoids _ _ (by decide) (by decide), marked_arithmetic_avoids⟩⟩

theorem callback_avoids : AvoidsCmd HW FactorAssignmentProgram.callback :=
  ⟨clear_callback_avoids, lift_low_avoids _ _ _ dispatcher_avoids,
    choose_avoids, clear_avoids _ (by decide), True.intro, True.intro, True.intro⟩

private theorem loop_avoids : AvoidsCmd HW FactorAssignmentProgram.loop :=
  avoids_record_iterate HW FactorAssignmentProgram.ports FactorAssignmentProgram.callback
    (by decide) (by decide) callback_avoids

private theorem product_avoids : AvoidsCmd HW FactorAssignmentProgram.product :=
  ⟨copy_avoids _ _ (by decide) (by decide), copy_avoids _ _ (by decide) (by decide),
    loop_avoids, move_avoids _ _ (by decide) (by decide)⟩

private theorem entry_ports_avoids : ∀ i ∈ FactorTableProgram.entryPorts, ¬ HW i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hj' := (Incidence.mem_workerPorts j).mp (List.mem_filter.mp hj).1
    exact SourceFrames.Table.base_avoids j (by omega)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem entry_scratch_avoids :
    ∀ i ∈ FactorAssignmentProgram.entryScratch, ¬ HW i := by
  intro i hi
  simp only [FactorAssignmentProgram.entryScratch, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact callback_scratch_avoids j hj
  · exact entry_ports_avoids i hi

private theorem initialize_avoids : AvoidsCmd HW FactorAssignmentProgram.initialize := by
  apply avoids_liftProgram
  exact avoids_compiled HW _ (avoids_clearMany HW _ entry_scratch_avoids) 175 854

/-- The fixed accepted-assignment implementation excludes bank744–767, including reads. -/
theorem assignment_avoids : AvoidsCmd HW FactorAssignmentProgram.assignment :=
  ⟨initialize_avoids, setup_avoids, product_avoids⟩

theorem program_avoids : AvoidsProgram HW FactorAssignmentProgram.program :=
  avoids_compiled HW _ assignment_avoids 175 854

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryFactorKeptFrame
