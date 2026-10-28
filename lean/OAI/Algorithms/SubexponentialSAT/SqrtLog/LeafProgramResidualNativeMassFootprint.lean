import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidual
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros

namespace OAI.Algorithms

/-! Tapes 320, 322 and 332 belong to the enclosing marked/branch sums. Every non-node residual
stage avoids both reading and writing them. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

 def outerTape (i : Fin 768) : Prop := i=320 ∨ i=322 ∨ i=332
 instance : DecidablePred outerTape := fun i => inferInstanceAs (Decidable (i=320 ∨ i=322 ∨ i=332))

 private theorem countPrepare_320 : (320 : Fin 768) ∉ Count.Prepare.ports :=
  Count.Prepare.ports_gap 320 (by norm_num) (by norm_num)
 private theorem countPrepare_322 : (322 : Fin 768) ∉ Count.Prepare.ports :=
  Count.Prepare.ports_gap 322 (by norm_num) (by norm_num)
 private theorem countPrepare_332 : (332 : Fin 768) ∉ Count.Prepare.ports :=
  Count.Prepare.port_332_not_mem

 attribute [local irreducible] Count.Prepare.ports

 theorem outer_high_avoids : AvoidsCmd outerTape LeafHighContextProgram.command := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

 theorem outer_clear_avoids (i : Fin 768) (hi : ¬outerTape i) :
    AvoidsCmd outerTape (LeafAssignmentSetupProgram.clear i) :=
  avoids_clearProgram outerTape i 0 1 hi

 theorem outer_collector_avoids (worker : Cmd 40 768) (hw : AvoidsCmd outerTape worker) :
    AvoidsProgram outerTape (LeafNodeSamplesProgram.collectProgram worker) := by
  apply avoids_compiled
  have hc (i : Fin 768) (hi : ¬outerTape i) : AvoidsCmd outerTape (LeafNodeSamplesProgram.clear i) :=
    avoids_clearProgram outerTape i 0 1 hi
  have ht (i j : Fin 768) (hi : ¬outerTape i) (hj : ¬outerTape j) :
      AvoidsCmd outerTape (LeafNodeSamplesProgram.transfer i j) :=
    avoids_transferProgram outerTape i j 0 1 hi hj
  have hp (i j : Fin 768) (hi : ¬outerTape i) (hj : ¬outerTape j) :
      AvoidsCmd outerTape (LeafNodeSamplesProgram.copy i j) :=
    avoids_copyProgram outerTape i j 305 0 1 hi hj (by decide)
  have hread : AvoidsCmd outerTape LeafNodeSamplesProgram.reader :=
    avoids_record_reader outerTape LeafNodeSamplesProgram.ports (by decide) (by decide)
  have hpop : AvoidsCmd outerTape LeafNodeSamplesProgram.pop := by
    change ¬outerTape 301
    decide
  have hinc : AvoidsCmd outerTape LeafNodeSamplesProgram.increment :=
    ⟨trivial,by change ¬outerTape 307; decide⟩
  have hcb : AvoidsCmd outerTape (LeafNodeSamplesProgram.callback worker) :=
    ⟨hp _ _ (by decide) (by decide),ht _ _ (by decide) (by decide),hw,
      ht _ _ (by decide) (by decide),hc _ (by decide),hinc⟩
  have hloop : AvoidsCmd outerTape (LeafNodeSamplesProgram.loop worker) := ⟨hread,hcb,hpop⟩
  exact ⟨hp _ _ (by decide) (by decide),hpop,hloop,hc _ (by decide),
    ht _ _ (by decide) (by decide),ht _ _ (by decide) (by decide),hc _ (by decide)⟩

 theorem outer_samples_avoids (hn : AvoidsCmd outerTape Node.command) :
    AvoidsCmd outerTape Samples.command :=
  ⟨⟨outer_clear_avoids _ (by decide),outer_clear_avoids _ (by decide)⟩,
    outer_collector_avoids _ hn⟩

 theorem outer_bank_clear_avoids (ps : List (Fin 768)) (hp : ∀ i∈ps,¬outerTape i) :
    AvoidsCmd outerTape (BankRoutines.clearCmd 699 (0 : Fin 40) 1 ps) := by
  induction ps with
  | nil => exact avoids_clearProgram outerTape 699 0 1 (by decide)
  | cons p ps ih => exact ⟨avoids_clearProgram outerTape p 0 1 (hp p (by simp)),
      ih (fun i hi => hp i (by simp [hi]))⟩

 theorem outer_prepare_avoids : AvoidsCmd outerTape Count.Prepare.command := by
  constructor
  · exact avoids_clearProgram outerTape 699 0 1 (by decide)
  · exact outer_bank_clear_avoids Count.Prepare.ports fun i hi hh => by
      rcases hh with rfl|rfl|rfl
      · exact countPrepare_320 hi
      · exact countPrepare_322 hi
      · exact countPrepare_332 hi

 theorem outer_count_avoids : AvoidsCmd outerTape Count.command := by
  refine ⟨?_,?_,avoids_clearProgram outerTape 5 0 1 (by decide),
    avoids_clearProgram outerTape 10 0 1 (by decide)⟩
  · apply avoids_call_lift_of_range
    intro i heq
    rcases heq with heq|heq|heq <;>
      have hv := congrArg Fin.val heq <;>
      change i.val=_ at hv <;> omega
  · apply avoids_liftProgram
    apply avoids_compiled
    refine ⟨?_,?_,?_⟩
    · apply avoids_call_lift_of_range
      intro i
      fin_cases i <;> decide
    · exact avoids_transferProgram _ 261 324 0 1 (by decide) (by decide)
    · exact avoids_transferProgram _ 324 323 0 1 (by decide) (by decide)

 theorem outer_finish_avoids : AvoidsCmd outerTape Residual.finish :=
  ⟨outer_clear_avoids _ (by decide),outer_clear_avoids _ (by decide),outer_clear_avoids _ (by decide)⟩

 theorem outer_command_avoids_of_node (hn : AvoidsCmd outerTape Node.command) :
    AvoidsCmd outerTape Residual.command :=
  ⟨outer_high_avoids,outer_samples_avoids hn,outer_prepare_avoids,outer_count_avoids,outer_finish_avoids⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
