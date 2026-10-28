import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeFinishReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros

/-! Actual query control commands exclude every read, peek and write in the
retained selector bank768..831. Calls into the original768-stack bank are
covered by their genuine port ranges, independently of their internal code. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorControlFrames

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open ProgramTapeReplay

/-- Every actual instruction of a lifted lower-bank program is disjoint from
the persistent selector interval. -/
theorem lowProgram_avoids {r l : ℕ} (p : Program r 768 l)
    (register : Fin r → Fin 40) :
    AvoidsProgram (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (ProgramLinking.liftProgram p register (Fin.castAdd 128)) := by
  apply avoids_liftProgram_of_range
  intro i hi
  change 768 ≤ i.val ∧ i.val < 832 at hi
  omega

theorem lowCommand_avoids {r : ℕ} (c : Cmd r 768) (input output : Fin 768)
    (register : Fin r → Fin 40) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (liftCommand c input output register (Fin.castAdd 128)) :=
  lowProgram_avoids (compiled c input output) register

private theorem isolated_avoids {r s l : ℕ}
    (p : Program r s l) (register : Fin r → Fin 16) (stack : Fin s → Fin 896)
    (tmp : Fin 896) (ports : List (Fin 896)) (inputs outputs : List (Fin 896 × Fin 896))
    (ht : ¬ (768 ≤ tmp.val ∧ tmp.val < 832))
    (hp : ∀ i ∈ ports, ¬ (768 ≤ i.val ∧ i.val < 832))
    (hi : ∀ q ∈ inputs, ¬ (768 ≤ q.1.val ∧ q.1.val < 832) ∧
      ¬ (768 ≤ q.2.val ∧ q.2.val < 832))
    (ho : ∀ q ∈ outputs, ¬ (768 ≤ q.1.val ∧ q.1.val < 832) ∧
      ¬ (768 ≤ q.2.val ∧ q.2.val < 832))
    (hs : ∀ i, ¬ (768 ≤ (stack i).val ∧ (stack i).val < 832)) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
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

private theorem bankClear_avoids {r : ℕ} (tmp : Fin 896)
    (value present : Fin r) (ports : List (Fin 896))
    (ht : ¬ (768 ≤ tmp.val ∧ tmp.val < 832))
    (hp : ∀ i ∈ ports, ¬ (768 ≤ i.val ∧ i.val < 832)) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram _ tmp value present ht
  | cons i ports ih =>
    exact ⟨avoids_clearProgram _ i value present (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

theorem countCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.countCommand := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · intro i
    fin_cases i <;> decide

theorem setupCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.setupCommand :=
  ⟨countCommand_avoids, avoids_clearMany _ _ (by norm_num [Fin.coe_ofNat_eq_mod]),
    avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide)⟩

theorem fillCommand_avoids (isE : Bool) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (PairNativeSetup.fillCommand isE) := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillInput, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillOutput, Fin.coe_ofNat_eq_mod]
  · intro i
    change ¬ (768 ≤ 325+i.val ∧ 325+i.val < 832)
    omega

theorem expandCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.expandCommand :=
  ⟨fillCommand_avoids true, fillCommand_avoids false⟩

theorem setupCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.setupCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ setupCommand_avoids _ _)

theorem expandCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.expandCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ expandCommand_avoids _ _)

theorem prepareHigh_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      HighQueryAdapter.prepareHigh := by
  refine ⟨⟨avoids_clearProgram _ _ _ _ (by decide),
    bankClear_avoids _ _ _ _ (by decide)
      (by norm_num [HighQueryAdapter.highChanged, Fin.coe_ofNat_eq_mod])⟩, ?_⟩
  apply avoids_liftProgram_of_range
  intro i
  fin_cases i <;> decide

theorem nativeLayoutLoad_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NativeLayoutLoad.command := by
  constructor
  · apply avoids_liftProgram
    apply avoids_compiled
    apply avoids_clearMany
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      change ¬ (768 ≤ j.val ∧ j.val < 832)
      omega
  · exact lowCommand_avoids _ _ _ _

theorem initializeNodes_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryAssembler.Nodes.initializeNodes := by
  refine ⟨lowCommand_avoids _ _ _ _, NodeFinishReplay.clearMany_avoids _ _ ?_⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> decide

theorem beginNode_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryAssembler.Nodes.beginNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, lowCommand_avoids _ _ _ _⟩
  intro i hi
  simp only [QueryAssembler.Nodes.nodeResetPorts, List.mem_cons, List.mem_nil_iff,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem readout_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeReadoutSpace.command := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      decide
    · have hs := NodeReadoutSpace.scratchPorts_low hi
      omega
  · apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide

/-- The exact paid scalar-cache copies are also used by the tuple-sum visitor. -/
theorem nodeAppendPrepare_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.prepare := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  · exact ⟨avoids_copyProgram _ 194 5 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 202 12 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 204 39 89 0 1 (by decide) (by decide) (by decide)⟩

theorem append_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.append :=
  ⟨avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 862 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 863 0 1 (by decide) (by decide)⟩

theorem nodeAppend_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.command :=
  ⟨nodeAppendPrepare_avoids, readout_avoids, append_avoids⟩

theorem finishNode_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryNodeFinish.finishNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ⟨⟨True.intro, ?_⟩, ?_⟩⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> decide
  · change ¬ (768 ≤ (307 : Fin 896).val ∧ (307 : Fin 896).val < 832)
    decide
  · change ¬ (768 ≤ (301 : Fin 896).val ∧ (301 : Fin 896).val < 832)
    decide

theorem nodeFinish_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryNodeFinish.command := ⟨nodeAppend_avoids, finishNode_avoids⟩

theorem handoff_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.handoff :=
  ⟨avoids_clearProgram _ 265 0 1 (by decide),
    avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 265 0 1 (by decide) (by decide)⟩

theorem reconstruction_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryReconstruction.command := ⟨handoff_avoids, lowCommand_avoids _ _ _ _⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorControlFrames
