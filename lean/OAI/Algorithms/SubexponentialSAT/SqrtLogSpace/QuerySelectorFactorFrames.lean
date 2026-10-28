import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepareFootprint
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros

/-! Every concrete source, factor, head, and preparation access avoids the
retained selector bank768..831. The certificates concern reads as well as
writes and therefore permit replay with unchanged steps and arbitrary selector
contents. All lower768 calls and relocated source calls are checked by their
actual physical stack maps. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFactorFrames
open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

local notation "H" => (fun i : Fin 896 => 768 ≤ Fin.val i ∧ Fin.val i < 832)

theorem low_port (i : Fin 768) : ¬ H (FactorAssignmentProgram.lowStack i) := by
  change ¬ (768 ≤ i.val ∧ i.val < 832)
  omega

theorem setup_avoids : AvoidsCmd H FactorAssignmentProgram.setup :=
  avoids_liftCommand_of_range H _ _ _ _ _ low_port

private theorem lift_low_avoids (c : Cmd 40 768) (input output : Fin 768) :
    AvoidsCmd H (FactorAssignmentProgram.liftLow c input output) :=
  avoids_liftCommand_of_range H _ _ _ _ _ low_port

namespace Table
open FactorTableProgram

theorem base_port (i : Fin 768) : ¬ H (basePort i) := by
  have hi := basePort_high i
  omega

theorem lift_base_avoids (c : Cmd 16 768) : AvoidsCmd H (liftBase c) :=
  avoids_liftCommand_of_range H _ _ _ _ _ base_port

theorem inner_avoids (c : Cmd 16 256) : AvoidsCmd H (liftInner c) := by
  apply avoids_liftCommand_of_range
  intro i
  change ¬ (768 ≤ 340+i.val ∧ 340+i.val < 832)
  omega

theorem specialize_avoids : AvoidsCmd H specializeCall := by
  refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide), ?_⟩
  apply avoids_liftCommand_of_range
  intro i
  change ¬ (768 ≤ 340+i.val ∧ 340+i.val < 832)
  omega

theorem low_payload_avoids : AvoidsCmd H lowPayload :=
  ⟨lift_base_avoids _, specialize_avoids⟩

theorem literal_payload_avoids : AvoidsCmd H literalPayload :=
  ⟨inner_avoids _, inner_avoids _, low_payload_avoids⟩

theorem literal_iteration_avoids : AvoidsCmd H literalIteration :=
  ⟨inner_avoids _, literal_payload_avoids, inner_avoids _⟩

theorem prepare_factor_avoids : AvoidsCmd H prepareFactor :=
  ⟨inner_avoids _, avoids_forCmd _ _ _ (by decide) literal_iteration_avoids,
    inner_avoids _⟩

theorem entry_ports_avoid : ∀ i ∈ entryPorts, ¬ H i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact base_port j
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem entry_avoids : AvoidsCmd H initializeWorker :=
  avoids_clearMany H _ entry_ports_avoid

theorem command_avoids : AvoidsCmd H command :=
  ⟨entry_avoids, lift_base_avoids _, prepare_factor_avoids, lift_base_avoids _⟩

theorem program_avoids : AvoidsProgram H program :=
  avoids_compiled H _ command_avoids _ _

theorem caller_avoids : AvoidsCmd H caller :=
  avoids_liftProgram H _ _ _ program_avoids
end Table

private theorem prepare_incidence_avoids :
    AvoidsCmd H FactorAssignmentProgram.prepareIncidence :=
  ⟨lift_low_avoids _ _ _, Table.caller_avoids⟩

private theorem choose_avoids : AvoidsCmd H FactorAssignmentProgram.choose :=
  ⟨⟨prepare_incidence_avoids, lift_low_avoids _ _ _⟩,
    ⟨prepare_incidence_avoids, lift_low_avoids _ _ _⟩, True.intro⟩

private theorem copy_avoids (src dst : Fin 896) (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (FactorAssignmentProgram.copy src dst) :=
  avoids_copyProgram H src dst 159 0 1 hs hd (by decide)

private theorem clear_avoids (src : Fin 896) (hs : ¬ H src) :
    AvoidsCmd H (FactorAssignmentProgram.clear src) :=
  avoids_clearProgram H src 0 1 hs

private theorem move_avoids (src dst : Fin 896) (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (FactorAssignmentProgram.move src dst) :=
  ⟨copy_avoids src dst hs hd, clear_avoids src hs⟩

theorem callback_avoids : AvoidsCmd H FactorAssignmentProgram.callback :=
  ⟨avoids_liftCommand_of_range H _ _ _ _ _ low_port,
    lift_low_avoids _ _ _, choose_avoids, clear_avoids _ (by decide),
    True.intro, True.intro, True.intro⟩

private theorem loop_avoids : AvoidsCmd H FactorAssignmentProgram.loop :=
  avoids_record_iterate H FactorAssignmentProgram.ports FactorAssignmentProgram.callback
    (by decide) (by decide) callback_avoids

private theorem product_avoids : AvoidsCmd H FactorAssignmentProgram.product :=
  ⟨copy_avoids _ _ (by decide) (by decide), copy_avoids _ _ (by decide) (by decide),
    loop_avoids, move_avoids _ _ (by decide) (by decide)⟩

private theorem entry_scratch_avoids :
    ∀ i ∈ FactorAssignmentProgram.entryScratch, ¬ H i := by
  intro i hi
  simp only [FactorAssignmentProgram.entryScratch, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact low_port j
  · exact Table.entry_ports_avoid i hi

private theorem initialize_avoids : AvoidsCmd H FactorAssignmentProgram.initialize := by
  apply avoids_liftProgram
  exact avoids_compiled H _ (avoids_clearMany H _ entry_scratch_avoids) 175 854

theorem assignment_avoids : AvoidsCmd H FactorAssignmentProgram.assignment :=
  ⟨initialize_avoids, setup_avoids, product_avoids⟩

theorem program_avoids : AvoidsProgram H FactorAssignmentProgram.program :=
  avoids_compiled H _ assignment_avoids 175 854

namespace Head
open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open HeadSumProgram
open HeadEvaluationProgram.StagedGate (copy clear)



private theorem bank_clear_avoids (tmp : Fin 896) (ports : List (Fin 896))
    (ht : ¬ H tmp) (hp : ∀ i ∈ ports, ¬ H i) :
    AvoidsCmd H (BankRoutines.clearCmd tmp (0 : Fin 40) 1 ports) := by
  induction ports with
  | nil => exact avoids_clearProgram H tmp 0 1 ht
  | cons i ports ih =>
    exact ⟨avoids_clearProgram H i 0 1 (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

private theorem copy_avoids (src dst : Fin 896) (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (copy src dst) := avoids_copyProgram H src dst 31 0 1 hs hd (by decide)

private theorem clear_avoids (src : Fin 896) (hs : ¬ H src) :
    AvoidsCmd H (clear src) := avoids_clearProgram H src 0 1 hs

theorem clearWork_avoids : AvoidsCmd H HeadSumAssembly.clearWork := by
  refine ⟨clear_avoids 31 (by decide), bank_clear_avoids 31 _ (by decide) ?_⟩
  intro i hi
  rw [HeadSumAssembly.mem_workPorts] at hi
  rcases hi with hi | hi
  · omega
  · simp only [HeadSumAssembly.controllerPorts, List.mem_cons, List.mem_nil_iff,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide

theorem overlay_avoids : AvoidsCmd H HighQueryAdapter.NativeOverlay.prepare := by
  refine ⟨⟨avoids_clearProgram H 875 0 1 (by decide),
    bank_clear_avoids 875 _ (by decide) ?_⟩, ?_⟩
  · norm_num [HighQueryAdapter.NativeOverlay.changed, Fin.coe_ofNat_eq_mod]
  · apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide

theorem accumulate_avoids : AvoidsCmd H accumulate := by
  refine ⟨?_, ?_⟩
  · apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide
  · apply avoids_liftProgram
    apply avoids_compiled
    apply avoids_clearMany
    norm_num [FactorEnvironment.environmentPorts, Function.comp_def, Fin.coe_ofNat_eq_mod]

theorem gate_avoids : AvoidsCmd H HeadEvaluationProgram.StagedGate.command := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨copy_avoids _ _ (by decide) (by decide),
      copy_avoids _ _ (by decide) (by decide), copy_avoids _ _ (by decide) (by decide),
      copy_avoids _ _ (by decide) (by decide), copy_avoids _ _ (by decide) (by decide),
      copy_avoids _ _ (by decide) (by decide)⟩
  · apply avoids_call_lift_of_range
    intro i
    change ¬ (768 ≤ i.val ∧ i.val < 832)
    have := i.isLt
    omega
  · exact ⟨clear_avoids _ (by decide), clear_avoids _ (by decide),
      clear_avoids _ (by decide), clear_avoids _ (by decide),
      clear_avoids _ (by decide), clear_avoids _ (by decide)⟩

private theorem counter_ports_avoid (p : CounterForPrograms.Ports 40 896)
    (hc : ¬ H p.counter) (hs : ¬ H p.scratch) (i : Fin 2) :
    ¬ H (CounterForPrograms.stackPorts p i) := by
  fin_cases i
  · exact hc
  · exact hs

/-- Every head-controller access is accounted for, including losing gates,
all binary counter tests and decrements, and final reclamation. -/
theorem head_avoids (accepted : Code) (ha : AvoidsCmd H accepted) :
    AvoidsCmd H (HeadSumAssembly.head accepted) := by
  have hpower : AvoidsCmd H power := by
    apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide
  have hseed : AvoidsCmd H seed :=
    ⟨copy_avoids _ _ (by decide) (by decide),
      copy_avoids _ _ (by decide) (by decide), hpower, clear_avoids _ (by decide)⟩
  have hinc : AvoidsCmd H (Counters.incrementCmd cursorPorts) :=
    avoids_call_lift_of_range H _ _ _ (counter_ports_avoid cursorPorts (by decide) (by decide))
  have hbody : AvoidsCmd H (body accepted) := ⟨gate_avoids, ⟨ha, True.intro⟩, hinc⟩
  have hzero : AvoidsCmd H (CounterForPrograms.zeroCmd fuelPorts) :=
    avoids_call_lift_of_range H _ _ _ (counter_ports_avoid fuelPorts (by decide) (by decide))
  have hdec : AvoidsCmd H (CounterForPrograms.decrementCmd fuelPorts) :=
    avoids_call_lift_of_range H _ _ _ (counter_ports_avoid fuelPorts (by decide) (by decide))
  have htest : AvoidsCmd H (CounterForPrograms.testCmd fuelPorts) := ⟨hzero, True.intro⟩
  have hloop : AvoidsCmd H (HeadSumProgram.command accepted) := ⟨htest, hbody, hdec, htest⟩
  have hfinal : AvoidsCmd H finalize := by
    apply avoids_liftProgram
    apply avoids_compiled
    apply avoids_clearMany
    norm_num [Function.comp_def, Fin.coe_ofNat_eq_mod]
  exact ⟨clearWork_avoids,
    avoids_compiled H _ (show AvoidsCmd H (scan accepted) from ⟨hseed, hloop, hfinal⟩) _ _⟩

theorem headProgram_avoids (accepted : Code) (ha : AvoidsCmd H accepted) :
    AvoidsProgram H (HeadSumAssembly.headProgram accepted) :=
  avoids_compiled H _ (head_avoids accepted ha) _ _

end Head

namespace Prepare

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open HighQueryAdapter

open SignatureHeadPrepareFootprint (bank_clear_avoids overwrite_avoids)

theorem key_avoids :
    AvoidsCmd H
      SignatureKeyNative.command := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem key_machine_avoids :
    AvoidsProgram H
      SignatureKeyNative.machine := key_avoids

theorem reset_avoids :
    AvoidsCmd H
      SignatureHeadPrepare.reset := by
  refine ⟨avoids_clearProgram _ 841 0 1 (by decide),
    bank_clear_avoids _ 841 0 1 _ (by decide) ?_⟩
  intro i hi
  simp only [SignatureHeadPrepare.cleared, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem masters_avoids :
    AvoidsCmd H
      SignatureHeadPrepare.masters :=
  ⟨overwrite_avoids _ 141 864 (by decide) (by decide) (by decide),
    overwrite_avoids _ 847 865 (by decide) (by decide) (by decide),
    overwrite_avoids _ 671 175 (by decide) (by decide) (by decide)⟩

theorem select_avoids :
    AvoidsCmd H
      NativeHeadSelect.select := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem selector_command_avoids :
    AvoidsCmd H
      NativeHeadSelect.command :=
  ⟨avoids_copyProgram _ 858 878 880 0 1 (by decide) (by decide) (by decide),
    avoids_copyProgram _ 670 879 880 0 1 (by decide) (by decide) (by decide),
    select_avoids⟩

theorem selector_reset_avoids :
    AvoidsCmd H
      NativeHeadSelect.reset := by
  refine ⟨avoids_clearProgram _ 880 0 1 (by decide),
    bank_clear_avoids _ 880 0 1 _ (by decide) ?_⟩
  intro i hi
  simp only [NativeHeadSelect.changed, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem selector_prepare_avoids :
    AvoidsCmd H
      NativeHeadSelect.prepare := ⟨selector_reset_avoids, selector_command_avoids⟩

theorem selector_program_avoids :
    AvoidsProgram H
      NativeHeadSelect.prepareProgram :=
  avoids_compiled _ _ selector_prepare_avoids 858 867

theorem command_avoids :
    AvoidsCmd H
      SignatureHeadPrepare.command :=
  ⟨reset_avoids, key_avoids, masters_avoids, selector_program_avoids⟩

theorem program_avoids :
    AvoidsProgram H
      SignatureHeadPrepare.program :=
  avoids_compiled _ _ command_avoids 838 866

end Prepare

/-- The accepted path is instantiated with the actual source-table assignment
and dense addition/reset programs, with no callback footprint premise. -/
theorem accepted_avoids : AvoidsCmd H HeadSumAssembly.accepted :=
  ⟨Head.overlay_avoids, assignment_avoids, Head.accumulate_avoids⟩

theorem head_avoids : AvoidsCmd H (HeadSumAssembly.head HeadSumAssembly.accepted) :=
  Head.head_avoids _ accepted_avoids

theorem head_program_avoids : AvoidsProgram H HeadAcceptedProgram.program :=
  Head.headProgram_avoids _ accepted_avoids

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFactorFrames
