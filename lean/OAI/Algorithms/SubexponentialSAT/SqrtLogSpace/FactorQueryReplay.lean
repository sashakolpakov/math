import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros

/-! The actual assignment program neither reads nor writes collector tapes320
and322. Certificates include the cache constructor, dispatcher peeks, source
specialization, arithmetic, parser iterations and all cleanup instructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorQueryReplay

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

local notation "H" => (fun i : Fin 768 => Fin.val i = 320 ∨ Fin.val i = 322)
local notation "HW" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322)

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
    change ¬ (340 + i.val = 320 ∨ 340 + i.val = 322)
    omega
  · simp

/-- The concrete constant encoder and every paid cache copy avoid the
collector words, including any temporary reads in their implementations. -/
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
  change ¬ (i.val = 320 ∨ i.val = 322)
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
  change ¬ (i.val = 320 ∨ i.val = 322)
  omega

private theorem hash_arithmetic_avoids : AvoidsCmd H FactorEvaluationSpace.hashArithmetic :=
  ⟨indicator_avoids, factor_clear_avoids _ (by decide),
    factor_clear_avoids _ (by decide), accumulate_avoids⟩

private theorem marked_arithmetic_avoids : AvoidsCmd H FactorEvaluationSpace.markedArithmetic :=
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

private theorem prepare_incidence_avoids :
    AvoidsCmd HW FactorAssignmentProgram.prepareIncidence :=
  ⟨lift_low_avoids _ _ _ factor_id_avoids, QuerySourceReplay.caller_avoids⟩

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
    have hh := QuerySourceReplay.Table.base_high j hj'.1
    omega
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

/-- No tape operation in the fixed accepted-assignment implementation touches
an outer collector tape. This includes reads, not only final-state framing. -/
theorem assignment_avoids : AvoidsCmd HW FactorAssignmentProgram.assignment :=
  ⟨initialize_avoids, setup_avoids, product_avoids⟩

theorem program_avoids : AvoidsProgram HW FactorAssignmentProgram.program :=
  avoids_compiled HW _ assignment_avoids 175 854

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorQueryReplay
