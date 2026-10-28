import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame

/-! The actual emitted-pair callback excludes reads, peeks and writes on832/833.
The mask words834/835 remain real callback inputs. This certificate does not
cover the enclosing pair controller, which operates on its own traversal words. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame.Factor
open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

local notation "H" => (fun i : Fin 896 => (Fin.val i = 832 ∨ Fin.val i = 833))

theorem low_port (i : Fin 768) : ¬ H (FactorAssignmentProgram.lowStack i) := by
  change ¬ ((i.val = 832 ∨ i.val = 833))
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
  change ¬ ((340+i.val = 832 ∨ 340+i.val = 833))
  omega

theorem specialize_avoids : AvoidsCmd H specializeCall := by
  refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide), ?_⟩
  apply avoids_liftCommand_of_range
  intro i
  change ¬ ((340+i.val = 832 ∨ 340+i.val = 833))
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
    change ¬ ((i.val = 832 ∨ i.val = 833))
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame.Factor

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame.Control
open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog ProgramTapeReplay

private theorem isolated_avoids {r s l : ℕ}
    (p : Program r s l) (register : Fin r → Fin 16) (stack : Fin s → Fin 896)
    (tmp : Fin 896) (ports : List (Fin 896)) (inputs outputs : List (Fin 896 × Fin 896))
    (ht : ¬ ((tmp.val = 832 ∨ tmp.val = 833)))
    (hp : ∀ i ∈ ports, ¬ ((i.val = 832 ∨ i.val = 833)))
    (hi : ∀ q ∈ inputs, ¬ ((q.1.val = 832 ∨ q.1.val = 833)) ∧
      ¬ ((q.2.val = 832 ∨ q.2.val = 833)))
    (ho : ∀ q ∈ outputs, ¬ ((q.1.val = 832 ∨ q.1.val = 833)) ∧
      ¬ ((q.2.val = 832 ∨ q.2.val = 833)))
    (hs : ∀ i, ¬ (((stack i).val = 832 ∨ (stack i).val = 833))) :
    AvoidsCmd (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      (isolated p register stack tmp ports inputs outputs) := by
  refine ⟨?_, avoids_liftProgram_of_range _ p register stack hs, ?_⟩
  · exact ⟨avoids_clearMany _ [tmp] (by simpa using ht),
      avoids_clearMany _ ports hp, avoids_resetMany _ workRegisters,
      avoids_copyMany _ tmp inputs ht hi⟩
  · refine ⟨avoids_clearMany _ (outputs.map Prod.snd) ?_,
      avoids_copyMany _ tmp outputs ht ho, avoids_clearMany _ ports hp,
      avoids_resetMany _ workRegisters⟩
    intro i h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact (ho q hq).2

theorem fillCommand_avoids (isE : Bool) :
    AvoidsCmd (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      (PairNativeSetup.fillCommand isE) := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillInput, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillOutput, Fin.coe_ofNat_eq_mod]
  · intro i
    change ¬ ((325+i.val = 832 ∨ 325+i.val = 833))
    omega

theorem expandCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      PairNativeSetup.expandCommand :=
  ⟨fillCommand_avoids true, fillCommand_avoids false⟩

theorem expandCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      PairNativeSetup.expandCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ expandCommand_avoids _ _)

theorem nodeAppendPrepare_avoids :
    AvoidsCmd (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      NodeAppendSpace.prepare := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  · exact ⟨avoids_copyProgram _ 194 5 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 202 12 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 204 39 89 0 1 (by decide) (by decide) (by decide)⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame.Control

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => (Fin.val i = 832 ∨ Fin.val i = 833))

theorem tuple_port (i : Fin 12) : ¬ H (tupleStacks i) := by
  change ¬ ((836 + i.val = 832 ∨ 836 + i.val = 833))
  omega

theorem copy_avoids (src dst tmp : Fin 896)
    (hs : ¬ H src) (hd : ¬ H dst) (ht : ¬ H tmp) :
    AvoidsCmd H (copyWord src dst tmp) :=
  avoids_copyProgram H src dst tmp 0 1 hs hd ht

theorem clear_avoids (src : Fin 896) (hs : ¬ H src) :
    AvoidsCmd H (clearWord src) :=
  avoids_clearProgram H src 0 1 hs

private structure SafeAvoids (c : Cmd 40 896) : Prop where
  proof : AvoidsCmd H c

private theorem SafeAvoids.intro {c : Cmd 40 896} (hc : AvoidsCmd H c) : SafeAvoids c :=
  ⟨hc⟩

private theorem SafeAvoids.seq {first second : Cmd 40 896}
    (hfirst : SafeAvoids first) (hsecond : SafeAvoids second) :
    SafeAvoids (.seq first second) :=
  ⟨⟨hfirst.proof, hsecond.proof⟩⟩

private theorem SafeAvoids.call {l : Nat} {p : Program 40 896 l}
    (hp : AvoidsProgram H p) :
    SafeAvoids (.call p) :=
  ⟨hp⟩

theorem clears_avoids (ports : List (Fin 896))
    (hp : ∀ i ∈ ports, ¬ H i) : AvoidsCmd H (clearWords ports) := by
  induction ports with
  | nil => exact True.intro
  | cons i is ih => exact ⟨clear_avoids i (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

theorem push_frame_avoids (src dst : Fin 896) (hne : src ≠ dst)
    (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (pushWordCommand src dst hne) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i
  · exact hs
  · exact hd

theorem pop_frame_avoids (src dst : Fin 896) (hne : src ≠ dst)
    (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (popWordCommand src dst hne) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i
  · exact hs
  · exact hd

theorem counter_ports_avoid (p : CounterForPrograms.Ports 40 896)
    (hc : ¬ H p.counter) (hs : ¬ H p.scratch) (i : Fin 2) :
    ¬ H (CounterForPrograms.stackPorts p i) := by
  fin_cases i
  · exact hc
  · exact hs

theorem counter_test_avoids (p : CounterForPrograms.Ports 40 896)
    (hc : ¬ H p.counter) (hs : ¬ H p.scratch) :
    AvoidsCmd H (CounterForPrograms.testCmd p) := by
  refine ⟨?_, True.intro⟩
  exact avoids_call_lift_of_range H _ _ _ (counter_ports_avoid p hc hs)

theorem counter_advance_avoids (p : CounterForPrograms.Ports 40 896)
    (hc : ¬ H p.counter) (hs : ¬ H p.scratch) :
    AvoidsCmd H (CounterForPrograms.advanceCmd p) := by
  refine ⟨?_, counter_test_avoids p hc hs⟩
  exact avoids_call_lift_of_range H _ _ _ (counter_ports_avoid p hc hs)

theorem advance_avoids : AvoidsCmd H advanceCommand := by
  refine ⟨?_, counter_advance_avoids remainingPorts (tuple_port 7) (tuple_port 5), True.intro⟩
  exact avoids_call_lift_of_range H _ _ _
    (counter_ports_avoid candidatePorts (tuple_port 2) (tuple_port 10))

theorem fuel_avoids : AvoidsCmd H initialFuelCommand :=
  avoids_call_lift_of_range H _ _ _
    (counter_ports_avoid initialFuelPorts (tuple_port 4) (tuple_port 7))

theorem reset_avoids : AvoidsCmd H resetCommand :=
  ⟨copy_avoids 651 _ _ (by decide) (tuple_port 2) (tuple_port 5),
    copy_avoids 651 _ _ (by decide) (tuple_port 4) (tuple_port 5),
    fuel_avoids, True.intro, True.intro⟩

theorem reset_generator_avoids : AvoidsCmd H resetGeneratorCommand :=
  ⟨reset_avoids, copy_avoids 651 _ _ (by decide) (tuple_port 8) (tuple_port 5)⟩

theorem save_cursor_avoids : AvoidsCmd H saveCursorCommand :=
  ⟨push_frame_avoids _ _ _ (tuple_port 2) (tuple_port 0),
    push_frame_avoids _ _ _ (tuple_port 7) (tuple_port 0)⟩

theorem restore_cursor_avoids : AvoidsCmd H restoreCursorCommand :=
  ⟨pop_frame_avoids _ _ _ (tuple_port 0) (tuple_port 7),
    pop_frame_avoids _ _ _ (tuple_port 0) (tuple_port 2)⟩

theorem record_representative_avoids : AvoidsCmd H recordRepresentativeCommand :=
  ⟨copy_avoids _ _ _ (tuple_port 2) (tuple_port 4) (tuple_port 5),
    push_frame_avoids _ _ _ (tuple_port 4) (tuple_port 1)⟩

theorem descend_level_avoids : AvoidsCmd H descendLevelCommand :=
  ⟨tuple_port 6, True.intro, tuple_port 9, tuple_port 6, True.intro⟩

theorem ascend_level_avoids : AvoidsCmd H ascendLevelCommand :=
  ⟨tuple_port 9, True.intro, tuple_port 6, True.intro⟩

theorem leave_head_avoids : AvoidsCmd H leaveHeadCommand := by
  apply clears_avoids
  intro i hi
  simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply tuple_port

theorem drop_representative_avoids : AvoidsCmd H dropRepresentativeCommand :=
  ⟨pop_frame_avoids _ _ _ (tuple_port 1) (tuple_port 4), clear_avoids _ (tuple_port 4)⟩

theorem test_parent_avoids : AvoidsCmd H testParentCommand := tuple_port 0

theorem test_available_avoids : AvoidsCmd H testAvailableCommand :=
  ⟨counter_test_avoids remainingPorts (tuple_port 7) (tuple_port 5), True.intro⟩

theorem initialize_levels_avoids : AvoidsCmd H initializeLevelsCommand :=
  ⟨copy_avoids 130 _ _ (by decide) (tuple_port 6) (tuple_port 5),
    copy_avoids 649 _ _ (by decide) (tuple_port 9) (tuple_port 5),
    tuple_port 6, True.intro, True.intro⟩

theorem initialize_fresh_avoids : AvoidsCmd H initializeFreshCommand :=
  ⟨clear_avoids _ (by decide), True.intro, show ¬ H (rescanStacks 22) from by decide⟩

theorem advance_candidate_avoids : AvoidsCmd H advanceCandidateCommand :=
  ⟨advance_avoids, clear_avoids _ (tuple_port 3)⟩

theorem reset_predecessor_avoids : AvoidsCmd H resetPredecessorCommand :=
  copy_avoids 651 _ _ (by decide) (tuple_port 8) (tuple_port 5)

theorem probe_avoids (predicate : Cmd 40 896) (hp : AvoidsCmd H predicate) :
    AvoidsCmd H (probeWith predicate) :=
  ⟨test_available_avoids, ⟨initialize_fresh_avoids, hp,
    show ¬ H (rescanStacks 22) from by decide⟩, True.intro⟩

theorem descend_avoids (loadHead : Cmd 40 896) (hl : AvoidsCmd H loadHead) :
    AvoidsCmd H (descendWith loadHead) :=
  ⟨record_representative_avoids, save_cursor_avoids, descend_level_avoids,
    leave_head_avoids, True.intro, hl, reset_generator_avoids⟩

theorem resume_parent_avoids (loadHead : Cmd 40 896) (hl : AvoidsCmd H loadHead) :
    AvoidsCmd H (resumeParentWith loadHead) :=
  ⟨drop_representative_avoids, restore_cursor_avoids, ascend_level_avoids,
    hl, reset_predecessor_avoids, advance_candidate_avoids⟩

theorem ascend_avoids (loadHead : Cmd 40 896) (hl : AvoidsCmd H loadHead) :
    AvoidsCmd H (ascendWith loadHead) :=
  ⟨leave_head_avoids, test_parent_avoids, resume_parent_avoids loadHead hl, True.intro⟩

theorem setup_avoids (loadHead : Cmd 40 896) (hl : AvoidsCmd H loadHead) :
    AvoidsCmd H (setupWith loadHead) := by
  refine ⟨?_, initialize_levels_avoids, True.intro, hl, reset_generator_avoids⟩
  apply clears_avoids
  intro i hi
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
  exact tuple_port j

/-- This covers the actual fixed attained-signature DFS, including all
presence tests, cursor scans and frame manipulation. -/
theorem tuple_controller_avoids (loadHead predicate visit : Cmd 40 896)
    (hl : AvoidsCmd H loadHead) (hp : AvoidsCmd H predicate)
    (hv : AvoidsCmd H visit) :
    AvoidsCmd H (SignatureTupleProgram.command controllerPorts
      (assembleRoutines loadHead predicate visit)) :=
  ⟨setup_avoids loadHead hl, ⟨hv, ascend_avoids loadHead hl⟩,
    probe_avoids predicate hp,
    ⟨descend_avoids loadHead hl, advance_candidate_avoids⟩,
    ascend_avoids loadHead hl⟩

private theorem SafeAvoids.tupleController
    {loadHead predicate visit : Cmd 40 896}
    (hl : SafeAvoids loadHead) (hp : SafeAvoids predicate)
    (hv : SafeAvoids visit) :
    SafeAvoids (SignatureTupleProgram.command controllerPorts
      (assembleRoutines loadHead predicate visit)) :=
  SafeAvoids.intro
    (tuple_controller_avoids loadHead predicate visit hl.proof hp.proof hv.proof)

theorem candidate_avoids : AvoidsCmd H candidateCall := by
  apply avoids_call_lift_of_range
  intro i
  change ¬ (((if i.val = 0 then 141 else if i.val = 15 then 847 else
    if i.val = 16 then 838 else if i.val = 17 then 839 else
    if i.val = 18 then 844 else 340 + i.val) = 832 ∨
    (if i.val = 0 then 141 else if i.val = 15 then 847 else
      if i.val = 16 then 838 else if i.val = 17 then 839 else
      if i.val = 18 then 844 else 340 + i.val) = 833))
  split_ifs <;> omega

theorem overwrite_avoids (src dst : Fin 896) (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (QueryTupleVisitor.overwrite src dst) :=
  ⟨avoids_clearProgram H dst 0 1 hd, copy_avoids src dst 841 hs hd (by decide)⟩

theorem replay_avoids (work : Cmd 40 896) (hw : AvoidsCmd H work) :
    AvoidsCmd H (QueryExecution.replay work) :=
  ⟨⟨overwrite_avoids 837 840 (by decide) (by decide),
    overwrite_avoids 845 843 (by decide) (by decide)⟩,
    show ¬ H 840 from by decide,
    ⟨pop_frame_avoids 840 838 (by decide) (by decide) (by decide),
      show ¬ H 843 from by decide⟩,
    hw, avoids_clearProgram H 838 0 1 (by decide), show ¬ H 840 from by decide⟩

private theorem SafeAvoids.replay {work : Cmd 40 896} (hw : SafeAvoids work) :
    SafeAvoids (QueryExecution.replay work) :=
  SafeAvoids.intro (replay_avoids work hw.proof)

theorem environment_avoids : AvoidsCmd H FactorEnvironment.bootstrap := by
  apply avoids_liftProgram
  apply avoids_compiled
  apply avoids_copyMany
  · decide
  · simp [FactorEnvironment.pairs, Fin.coe_ofNat_eq_mod]

theorem clear_pair_avoids : AvoidsCmd H QueryAssembler.clearPair := by
  apply avoids_liftProgram
  apply avoids_compiled
  apply avoids_clearMany
  intro i hi
  have hh := (QueryAssembler.pairScratch_mem i).mp hi
  rcases hh with hh | hh | rfl | rfl | rfl | rfl
  · change ¬ H i
    omega
  · change ¬ H i
    omega
  all_goals decide

theorem pair_sign_avoids : AvoidsCmd H QueryProgram.pairSignCall := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem signed_accumulate_avoids : AvoidsCmd H QueryProgram.signedAccumulate := by
  constructor
  · apply avoids_call_lift_of_range
    intro i
    change ¬ H (QueryProgram.leafScalePorts i)
    simp only [QueryProgram.leafScalePorts]
    split_ifs <;> simp only [Fin.coe_ofNat_eq_mod] <;> have hi := i.isLt <;> omega
  · apply avoids_call_lift_of_range
    intro i
    change ¬ H (QueryProgram.leafNormalizePorts i)
    simp only [QueryProgram.leafNormalizePorts]
    split_ifs <;> simp only [Fin.coe_ofNat_eq_mod] <;> have hi := i.isLt <;> omega

theorem pair_update_avoids : AvoidsCmd H QueryProgram.pairUpdate :=
  ⟨pair_sign_avoids, signed_accumulate_avoids, show ¬ H 848 from by decide⟩

theorem commit_pair_avoids : AvoidsCmd H QueryAssembler.commitPair :=
  ⟨⟨clear_pair_avoids, environment_avoids,
    overwrite_avoids 211 34 (by decide) (by decide)⟩,
    pair_update_avoids, clear_pair_avoids⟩


theorem tuple_clear_bank_avoids (ports : List (Fin 896))
    (hp : ∀ i ∈ ports, ¬ H i) : AvoidsCmd H (QueryTupleInit.clearBank ports) := by
  apply avoids_liftProgram
  apply avoids_compiled
  exact avoids_clearMany H ports hp

theorem factor_move_avoids (K : Fin 768 → Prop) (src dst : Fin 768)
    (hs : ¬ K src) (hd : ¬ K dst) (ht : ¬ K 159) :
    AvoidsCmd K (SqrtLog.LeafProgram.Factor.move src dst) :=
  ⟨avoids_copyProgram K src dst 159 0 1 hs hd ht,
    avoids_clearProgram K src 0 1 hs⟩

theorem tuple_multiply_call_avoids : AvoidsCmd H QueryAssembler.TupleMultiply.multiply := by
  apply avoids_liftProgram
  apply avoids_compiled
  refine ⟨factor_move_avoids _ 67 61 (by decide) (by decide) (by decide),
    factor_move_avoids _ 151 67 (by decide) (by decide) (by decide), ?_,
    factor_move_avoids _ 67 151 (by decide) (by decide) (by decide)⟩
  apply avoids_call_lift_of_range
  intro i
  change ¬ H (QueryAssembler.TupleMultiply.ports (SqrtLog.LeafProgram.Factor.nativeStacks i))
  simp only [QueryAssembler.TupleMultiply.ports]
  split_ifs
  · decide
  · decide
  · change ¬ ((i.val = 832 ∨ i.val = 833))
    have hi := i.isLt
    omega

theorem tuple_multiply_avoids : AvoidsCmd H QueryAssembler.TupleMultiply.command := by
  refine ⟨⟨NodeFinishReplay.clearMany_avoids H [61,70] ?_,
    clear_pair_avoids, environment_avoids⟩,
    tuple_multiply_call_avoids, clear_pair_avoids⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl <;> decide


open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

private theorem loader_clearMany_avoids (ps : List (Fin 896))
    (hp : ∀ p ∈ ps, ¬ ((p.val = 832 ∨ p.val = 833))) :
    AvoidsCmd (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833)) (clearMany ps) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨avoids_clearProgram _ p 0 1 (hp p (by simp)),
      ih (fun q hq => hp q (by simp [hq]))⟩

theorem lower_avoids {r l : ℕ} (p : Program r 768 l) (reg : Fin r → Fin 40) :
    AvoidsProgram (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      (ProgramLinking.liftProgram p reg SignatureHeadLoader.lowStacks) := by
  apply avoids_liftProgram_of_range
  intro i hi
  have hv := i.isLt
  change (i.val = 832 ∨ i.val = 833) at hi
  omega

theorem programFrom_avoids (src : Fin 896) (hs : ¬ ((src.val = 832 ∨ src.val = 833))) :
    AvoidsProgram (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      (SignatureHeadLoader.programFrom src) := by
  apply avoids_liftProgram
  apply avoids_compiled
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_⟩
  · exact loader_clearMany_avoids [649,659,846,847] (by norm_num [Fin.coe_ofNat_eq_mod])
  · exact avoids_copyProgram _ src 649 659 0 1 hs (by decide) (by decide)
  · apply avoids_liftProgram_of_range
    intro i hi
    have hv := i.isLt
    change (i.val = 832 ∨ i.val = 833) at hi
    omega
  · exact avoids_clearProgram _ 659 0 1 (by decide)
  · exact avoids_copyProgram _ 668 847 659 0 1 (by decide) (by decide) (by decide)
  · exact loader_clearMany_avoids [668,669,846] (by norm_num [Fin.coe_ofNat_eq_mod])

theorem program843_avoids :
    AvoidsProgram (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      (SignatureHeadLoader.programFrom 843) := programFrom_avoids 843 (by decide)

theorem program845_avoids :
    AvoidsProgram (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      (SignatureHeadLoader.programFrom 845) := programFrom_avoids 845 (by decide)


theorem tuple_sum_avoids : AvoidsCmd H QueryTupleSum.command := by
  refine ⟨⟨QueryPairControlFrame.Control.nodeAppendPrepare_avoids,
    NodeFinishReplay.clearMany_avoids H _ ?_⟩, ?_⟩
  · intro i hi
    have hh := QueryTupleSum.scratchPorts_low hi
    omega
  · apply avoids_call_lift_of_range
    intro i
    change ¬ H (QueryTupleSum.ports i)
    simp only [QueryTupleSum.ports]
    split_ifs <;> simp only [Fin.coe_ofNat_eq_mod] <;> have hi := i.isLt <;> omega

theorem tuple_end_avoids : AvoidsCmd H QueryExecution.TupleEnd.command := by
  refine ⟨tuple_sum_avoids, tuple_clear_bank_avoids _ ?_⟩
  intro i hi
  simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply tuple_port

theorem pair_start_avoids : AvoidsCmd H QueryExecution.PairStart.command :=
  ⟨clear_avoids 851 (by decide), QueryPairControlFrame.Control.expandCaller_avoids⟩

theorem representative_install_avoids : AvoidsCmd H QueryTupleVisitor.installRepresentative :=
  ⟨overwrite_avoids 838 859 (by decide) (by decide),
    avoids_compiled H _ (QueryPairControlFrame.Factor.Head.overlay_avoids) _ _,
    overwrite_avoids 145 869 (by decide) (by decide),
    avoids_clearProgram H 859 0 1 (by decide)⟩

theorem tuple_init_avoids
    (hsetup : AvoidsCmd H FactorAssignmentProgram.setup) :
    AvoidsCmd H QueryTupleInit.command := by
  have hlo : ∀ i ∈ QueryTupleInit.lowPorts, ¬ H i := by
    intro i hi
    have hh := (QueryTupleInit.mem_lowPorts i).mp hi
    omega
  refine ⟨tuple_clear_bank_avoids _ ?_, hsetup,
    overwrite_avoids 69 852 (by decide) (by decide),
    overwrite_avoids 703 869 (by decide) (by decide),
    tuple_clear_bank_avoids _ hlo⟩
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hlo i hi
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst i
    decide


theorem head_sum_avoids : AvoidsCmd H (HeadSumAssembly.head HeadSumAssembly.accepted) :=
  QueryPairControlFrame.Factor.head_avoids

theorem concrete_tuple_init_avoids : AvoidsCmd H QueryTupleInit.command :=
  tuple_init_avoids (QueryPairControlFrame.Factor.setup_avoids)

theorem head_prepare_avoids : AvoidsCmd H SignatureHeadPrepare.command :=
  QueryPairControlFrame.Factor.Prepare.command_avoids

/-- The fixed visitor composes the actual two passes and all arithmetic
without any access to the two suspended pair traversal words. -/
theorem visitor_avoids_of_loader
    (hload : AvoidsProgram H (SignatureHeadLoader.programFrom 843)) :
    AvoidsCmd H QueryVisitorProgram.visitor := by
  have hload' := SafeAvoids.call hload
  have hbaselineSafe := hload'.seq (SafeAvoids.intro representative_install_avoids)
  have hbaseline : AvoidsCmd H QueryVisitorProgram.baselineHead := by
    have hpack : ∃ c, c=QueryVisitorProgram.baselineHead ∧ SafeAvoids c := by
      refine ⟨_,?_,hbaselineSafe⟩
      rw [QueryVisitorProgram.baselineHead]
    obtain ⟨_,rfl,hc⟩ := hpack
    exact hc.proof
  have hevaluateSafe := hload'.seq ((SafeAvoids.intro head_prepare_avoids).seq
    ((SafeAvoids.intro head_sum_avoids).seq (SafeAvoids.intro tuple_multiply_avoids)))
  have hevaluate : AvoidsCmd H QueryVisitorProgram.evaluateHead := by
    have hpack : ∃ c, c=QueryVisitorProgram.evaluateHead ∧ SafeAvoids c := by
      refine ⟨_,?_,hevaluateSafe⟩
      rw [QueryVisitorProgram.evaluateHead,QueryVisitorProgram.loadHead,
        QueryVisitorProgram.evaluateLoadedHead]
    obtain ⟨_,rfl,hc⟩ := hpack
    exact hc.proof
  have hvisitor := (SafeAvoids.intro concrete_tuple_init_avoids).seq
    ((SafeAvoids.intro hbaseline).replay.seq
      ((SafeAvoids.intro hevaluate).replay.seq (SafeAvoids.intro tuple_end_avoids)))
  have hpack : ∃ c, c=QueryVisitorProgram.visitor ∧ SafeAvoids c := by
    refine ⟨_,?_,hvisitor⟩
    rw [QueryVisitorProgram.visitor]
  obtain ⟨_,rfl,hc⟩ := hpack
  exact hc.proof

theorem tuple_avoids_of_loader
    (hload : AvoidsProgram H (SignatureHeadLoader.programFrom 845))
    (hvisit : AvoidsCmd H QueryVisitorProgram.visitor) :
    AvoidsCmd H SignatureTupleComplete.command := by
  have htuple := (SafeAvoids.call hload).tupleController
    (SafeAvoids.intro candidate_avoids) (SafeAvoids.intro hvisit)
  have hpack : ∃ c, c=SignatureTupleComplete.command ∧ SafeAvoids c := by
    refine ⟨_,?_,htuple⟩
    rw [SignatureTupleComplete.command,SignatureTupleComplete.routines,
      SignatureTupleLoader.loadHead,SignatureTupleLoader.headAddress]
  obtain ⟨_,rfl,hc⟩ := hpack
  exact hc.proof


theorem visitor_avoids : AvoidsCmd H QueryVisitorProgram.visitor :=
  visitor_avoids_of_loader program843_avoids

theorem tuple_avoids : AvoidsCmd H SignatureTupleComplete.command :=
  tuple_avoids_of_loader program845_avoids visitor_avoids

private theorem tuple_safe : SafeAvoids SignatureTupleComplete.command :=
  ⟨tuple_avoids⟩

private theorem callback_safe : SafeAvoids QueryStreamProgram.pairCallback := by
  let hs := (SafeAvoids.intro (c := QueryExecution.PairStart.command)
      pair_start_avoids).seq
    (tuple_safe.seq (SafeAvoids.intro (c := QueryAssembler.commitPair)
      commit_pair_avoids))
  have hpack : ∃ c, c = QueryStreamProgram.pairCallback ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [QueryStreamProgram.pairCallback]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc

theorem callback_avoids : AvoidsCmd H QueryStreamProgram.pairCallback :=
  callback_safe.proof

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame
