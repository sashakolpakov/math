import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryFactorKeptFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackFrames

/-! Concrete preservation of the retained interval744..767 by the fixed
conditioned query. Every certificate examines actual call ports. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.Loader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem copyMany_avoids {s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s × Fin s)) (ht : ¬ H tmp)
    (hp : ∀ p∈ps,¬ H p.1 ∧ ¬ H p.2) : AvoidsCmd H (copyMany tmp ps) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨avoids_copyProgram H p.1 p.2 tmp 0 1 (hp p (by simp)).1
      (hp p (by simp)).2 ht,ih (fun q hq=>hp q (by norm_num [hq]))⟩

private theorem clearMany_avoids {s : ℕ} (H : Fin s → Prop) (ps : List (Fin s))
    (hp : ∀ p∈ps,¬ H p) : AvoidsCmd H (clearMany ps) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨avoids_clearProgram H p 0 1 (hp p (by simp)),ih (fun q hq=>hp q (by norm_num [hq]))⟩

private theorem resetMany_avoids {s : ℕ} (H : Fin s → Prop) (rs : List (Fin 16)) :
    AvoidsCmd H (resetMany (S:=s) rs) := by
  induction rs with
  | nil => exact True.intro
  | cons r rs ih => exact ⟨True.intro,ih⟩

private theorem prepare_avoids {s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s)) (ins : List (Fin s × Fin s))
    (ht : ¬ H tmp) (hp : ∀ p∈ps,¬ H p) (hi : ∀ p∈ins,¬ H p.1 ∧ ¬ H p.2) :
    AvoidsCmd H (prepare tmp ps ins) :=
  ⟨clearMany_avoids H [tmp] (by simpa using ht),clearMany_avoids H ps hp,
    resetMany_avoids H workRegisters,copyMany_avoids H tmp ins ht hi⟩

private theorem finish_avoids {s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s)) (outs : List (Fin s × Fin s))
    (ht : ¬ H tmp) (hp : ∀ p∈ps,¬ H p) (ho : ∀ p∈outs,¬ H p.1 ∧ ¬ H p.2) :
    AvoidsCmd H (finish tmp ps outs) := by
  refine ⟨clearMany_avoids H (outs.map Prod.snd) ?_,copyMany_avoids H tmp outs ht ho,
    clearMany_avoids H ps hp,resetMany_avoids H workRegisters⟩
  intro q hq
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
  exact (ho p hp).2

private theorem work_avoids {s : ℕ} (hs : s≤288) (i : Fin s) :
    ¬ (744 ≤ (workPort hs i).val ∧ (workPort hs i).val < 768) := by
  simp only [workPort]
  omega

private theorem stage_avoids {r s l : ℕ} (p : Program r s l) (reg : Fin r → Fin 16)
    (hs : s≤288) (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (hi : ∀ q∈ins,¬ (744 ≤ q.1.val ∧ q.1.val < 768))
    (ho : ∀ q∈outs,¬ (744 ≤ q.2.val ∧ q.2.val < 768)) :
    AvoidsCmd (fun i : Fin 768=>744 ≤ i.val ∧ i.val < 768) (stage p reg hs ins outs) := by
  let H := fun i : Fin 768=>744 ≤ i.val ∧ i.val < 768
  have ht : ¬ H temporary := by decide
  have hw : ∀ i∈workPorts hs,¬ H i := by
    intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    exact work_avoids hs j
  have hin : ∀ q∈inputCopies hs ins,¬ H q.1 ∧ ¬ H q.2 := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    exact ⟨hi z hz,work_avoids hs z.2⟩
  have hout : ∀ q∈outputCopies hs outs,¬ H q.1 ∧ ¬ H q.2 := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    exact ⟨work_avoids hs z.1,ho z hz⟩
  exact ⟨prepare_avoids H temporary (workPorts hs) (inputCopies hs ins) ht hw hin,
    avoids_liftProgram_of_range H p reg (workPort hs) (work_avoids hs),
    finish_avoids H temporary (workPorts hs) (outputCopies hs outs) ht hw hout⟩

theorem prepareHead_avoids :
    AvoidsCmd (fun i : Fin 768=>744 ≤ i.val ∧ i.val < 768) prepareHead := by
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · exact stage_avoids _ _ _ _ _ (by norm_num [headInputs]) (by norm_num [headOutputs])
  · exact stage_avoids _ _ _ _ _ (by norm_num [countInputs]) (by norm_num [countOutputs])
  · exact stage_avoids _ _ _ _ _ (by norm_num [scatterInputs]) (by norm_num [scatterOutputs])
  · exact stage_avoids _ _ _ _ _ (by norm_num [factorInputs]) (by norm_num [factorOutputs])

theorem bootstrap_avoids :
    AvoidsProgram (fun i : Fin 768=>744 ≤ i.val ∧ i.val < 768) SignatureHeadLoader.bootstrapProgram := by
  apply avoids_compiled
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · exact stage_avoids _ _ _ _ _ (by norm_num [addressInputs]) (by norm_num [addressOutputs])
  · exact stage_avoids _ _ _ _ _ (by norm_num [rowCountInputs]) (by norm_num [rowCountOutputs])
  · exact stage_avoids _ _ _ _ _ (by norm_num [cacheInputs]) (by norm_num [cacheOutputs])
  · exact clearMany_avoids _ retainedPorts (by norm_num [retainedPorts])
  · exact copyMany_avoids _ temporary retainedCopies (by decide) (by norm_num [retainedCopies])

theorem local_avoids :
    AvoidsProgram (fun i : Fin 768=>744 ≤ i.val ∧ i.val < 768) SignatureHeadLoader.localProgram := by
  apply avoids_compiled
  refine ⟨prepareHead_avoids,?_,?_,?_⟩
  · exact stage_avoids _ _ _ _ _ (by norm_num [SignatureHeadLoader.matrixInputs])
      (by norm_num [SignatureHeadLoader.rawOutputs])
  · exact stage_avoids _ _ _ _ _ (by norm_num [SignatureHeadLoader.shiftInputs])
      (by norm_num [SignatureHeadLoader.shiftOutputs])
  · exact avoids_clearProgram _ 669 0 1 (by decide)

theorem programFrom_avoids (src : Fin 896) (hs : ¬ (744 ≤ src.val ∧ src.val < 768)) :
    AvoidsProgram (fun i : Fin 896=>744 ≤ i.val ∧ i.val < 768) (SignatureHeadLoader.programFrom src) := by
  apply avoids_liftProgram
  apply avoids_compiled
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_⟩
  · exact clearMany_avoids _ [649,659,846,847] (by simp)
  · exact avoids_copyProgram _ src 649 659 0 1 hs (by decide) (by decide)
  · apply avoids_liftProgram
    exact local_avoids
  · exact avoids_clearProgram _ 659 0 1 (by decide)
  · exact avoids_copyProgram _ 668 847 659 0 1 (by decide) (by decide) (by decide)
  · exact clearMany_avoids _ [668,669,846] (by simp)

theorem program843_avoids :
    AvoidsProgram (fun i : Fin 896=>744 ≤ i.val ∧ i.val < 768) (SignatureHeadLoader.programFrom 843) :=
  programFrom_avoids 843 (by decide)

theorem program845_avoids :
    AvoidsProgram (fun i : Fin 896=>744 ≤ i.val ∧ i.val < 768) (SignatureHeadLoader.programFrom 845) :=
  programFrom_avoids 845 (by decide)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.Loader

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.Factor
open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
local notation "H" => (fun i : Fin 896 => 744 ≤ Fin.val i ∧ Fin.val i < 768)
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
    change ¬ (744 ≤ i.val ∧ i.val < 768)
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
  ⟨Head.overlay_avoids, QueryFactorKeptFrame.assignment_avoids, Head.accumulate_avoids⟩

theorem head_avoids : AvoidsCmd H (HeadSumAssembly.head HeadSumAssembly.accepted) :=
  Head.head_avoids _ accepted_avoids

theorem head_program_avoids : AvoidsProgram H HeadAcceptedProgram.program :=
  Head.headProgram_avoids _ accepted_avoids


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.Factor

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.Control

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open ProgramTapeReplay

theorem lowCommand_avoids {r : ℕ} (c : Cmd r 768) (input output : Fin 768)
    (register : Fin r → Fin 40)
    (hc : AvoidsCmd (fun i : Fin 768 => 744 ≤ i.val ∧ i.val < 768) c) :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      (liftCommand c input output register (Fin.castAdd 128)) := by
  apply avoids_liftProgram
  exact avoids_compiled _ _ hc _ _

private theorem isolated_avoids {r s l : ℕ}
    (p : Program r s l) (register : Fin r → Fin 16) (stack : Fin s → Fin 896)
    (tmp : Fin 896) (ports : List (Fin 896)) (inputs outputs : List (Fin 896 × Fin 896))
    (ht : ¬ (744 ≤ tmp.val ∧ tmp.val < 768))
    (hp : ∀ i ∈ ports, ¬ (744 ≤ i.val ∧ i.val < 768))
    (hi : ∀ q ∈ inputs, ¬ (744 ≤ q.1.val ∧ q.1.val < 768) ∧
      ¬ (744 ≤ q.2.val ∧ q.2.val < 768))
    (ho : ∀ q ∈ outputs, ¬ (744 ≤ q.1.val ∧ q.1.val < 768) ∧
      ¬ (744 ≤ q.2.val ∧ q.2.val < 768))
    (hs : ∀ i, ¬ (744 ≤ (stack i).val ∧ (stack i).val < 768)) :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
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
    (ht : ¬ (744 ≤ tmp.val ∧ tmp.val < 768))
    (hp : ∀ i ∈ ports, ¬ (744 ≤ i.val ∧ i.val < 768)) :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram _ tmp value present ht
  | cons i ports ih =>
    exact ⟨avoids_clearProgram _ i value present (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

theorem countCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      PairNativeSetup.countCommand := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · intro i
    fin_cases i <;> decide

theorem setupCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      PairNativeSetup.setupCommand :=
  ⟨countCommand_avoids, avoids_clearMany _ _ (by norm_num [Fin.coe_ofNat_eq_mod]),
    avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide)⟩

theorem fillCommand_avoids (isE : Bool) :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      (PairNativeSetup.fillCommand isE) := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillInput, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillOutput, Fin.coe_ofNat_eq_mod]
  · intro i
    change ¬ (744 ≤ 325+i.val ∧ 325+i.val < 768)
    omega

theorem expandCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      PairNativeSetup.expandCommand :=
  ⟨fillCommand_avoids true, fillCommand_avoids false⟩

theorem setupCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      PairNativeSetup.setupCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ setupCommand_avoids _ _)

theorem expandCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      PairNativeSetup.expandCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ expandCommand_avoids _ _)

theorem prepareHigh_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      HighQueryAdapter.prepareHigh := by
  refine ⟨⟨avoids_clearProgram _ _ _ _ (by decide),
    bankClear_avoids _ _ _ _ (by decide)
      (by norm_num [HighQueryAdapter.highChanged, Fin.coe_ofNat_eq_mod])⟩, ?_⟩
  apply avoids_liftProgram_of_range
  intro i
  fin_cases i <;> decide

theorem nativeLayoutLoad_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
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
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp ‹j ∈ SqrtLog.LeafProgram.LayoutMasters.lowPorts›
      change ¬ (744 ≤ 128+k.val ∧ 128+k.val < 768)
      omega
  · apply lowCommand_avoids
    apply avoids_liftProgram
    apply avoids_compiled
    apply avoids_copyMany
    · decide
    · intro q hq
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
      change (¬ (744 ≤ 730+j.val ∧ 730+j.val < 768)) ∧
        ¬ (744 ≤ 128+j.val ∧ 128+j.val < 768)
      omega

theorem initializeNodes_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      QueryAssembler.Nodes.initializeNodes := by
  refine ⟨lowCommand_avoids _ _ _ _ ?_, NodeFinishReplay.clearMany_avoids _ _ ?_⟩
  · exact ⟨avoids_clearProgram _ 301 0 1 (by decide),
      avoids_clearProgram _ 302 0 1 (by decide),
      avoids_clearProgram _ 305 0 1 (by decide),
      avoids_clearProgram _ 307 0 1 (by decide),
      avoids_clearProgram _ 78 0 1 (by decide),
      avoids_copyProgram _ 300 301 305 0 1 (by decide) (by decide) (by decide)⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> decide

theorem beginNode_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      QueryAssembler.Nodes.beginNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, lowCommand_avoids _ _ _ _ ?_⟩
  · intro i hi
    simp only [QueryAssembler.Nodes.nodeResetPorts, List.mem_cons, List.mem_nil_iff,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine ⟨?_, avoids_record_reader _ SqrtLog.LeafNodeSamplesProgram.ports
      (by decide) (by decide), avoids_transferProgram _ 302 78 0 1 (by decide) (by decide)⟩
    change ¬ (744 ≤ (301 : Fin 768).val ∧ (301 : Fin 768).val < 768)
    decide
/-- Physical readout uses only its explicit scalar bank. -/


theorem readout_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
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
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      NodeAppendSpace.prepare := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  · exact ⟨avoids_copyProgram _ 194 5 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 202 12 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 204 39 89 0 1 (by decide) (by decide) (by decide)⟩

theorem append_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      NodeAppendSpace.append :=
  ⟨avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 862 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 863 0 1 (by decide) (by decide)⟩

theorem nodeAppend_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      NodeAppendSpace.command :=
  ⟨nodeAppendPrepare_avoids, readout_avoids, append_avoids⟩

theorem finishNode_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      QueryNodeFinish.finishNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ⟨⟨True.intro, ?_⟩, ?_⟩⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> decide
  · change ¬ (744 ≤ (307 : Fin 896).val ∧ (307 : Fin 896).val < 768)
    decide
  · change ¬ (744 ≤ (301 : Fin 896).val ∧ (301 : Fin 896).val < 768)
    decide

theorem nodeFinish_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      QueryNodeFinish.command := ⟨nodeAppend_avoids, finishNode_avoids⟩

theorem handoff_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      NodeAppendSpace.handoff :=
  ⟨avoids_clearProgram _ 265 0 1 (by decide),
    avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 265 0 1 (by decide) (by decide)⟩

theorem reconstruction_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      QueryReconstruction.command := by
  refine ⟨handoff_avoids, lowCommand_avoids _ _ _ _ ⟨?_, ?_⟩⟩
  · unfold SqrtLog.LeafProgram.Count.Prepare.command
    generalize hports : SqrtLog.LeafProgram.Count.Prepare.ports = ports
    refine ⟨avoids_clearProgram _ 699 0 1 (by decide), ?_⟩
    have clear (ps : List (Fin 768))
        (hp : ∀ i ∈ ps, ¬ (744 ≤ i.val ∧ i.val < 768)) :
        AvoidsCmd (fun i : Fin 768 => 744 ≤ i.val ∧ i.val < 768)
          (BankRoutines.clearCmd 699 (0 : Fin 40) 1 ps) := by
      induction ps with
      | nil => exact avoids_clearProgram _ 699 0 1 (by decide)
      | cons i ps ih =>
          exact ⟨avoids_clearProgram _ i 0 1 (hp i (by simp)),
            ih (fun j hj => hp j (by simp [hj]))⟩
    exact clear ports (by
      intro i hi
      rw [← hports] at hi
      have hh := SqrtLog.LeafProgram.Count.Prepare.ports_lt i hi
      omega)
  · refine ⟨?_, ?_, avoids_clearProgram _ 5 0 1 (by decide),
      avoids_clearProgram _ 10 0 1 (by decide)⟩
    · apply avoids_call_lift_of_range
      intro i
      change ¬ (744 ≤ i.val ∧ i.val < 768)
      omega
    · apply avoids_call_lift_of_range
      intro i
      change ¬ (744 ≤ i.val ∧ i.val < 768)
      omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.Control

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => 744 ≤ Fin.val i ∧ Fin.val i < 768)

theorem tuple_port (i : Fin 12) : ¬ H (tupleStacks i) := by
  change ¬ (744 ≤ 836 + i.val ∧ 836 + i.val < 768)
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
  fin_cases i <;> decide

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
  · change ¬ (744 ≤ i.val ∧ i.val < 768)
    have hi := i.isLt
    omega

theorem tuple_multiply_avoids : AvoidsCmd H QueryAssembler.TupleMultiply.command := by
  refine ⟨⟨NodeFinishReplay.clearMany_avoids H [61,70] ?_,
    clear_pair_avoids, environment_avoids⟩,
    tuple_multiply_call_avoids, clear_pair_avoids⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl <;> decide


theorem tuple_sum_avoids : AvoidsCmd H QueryTupleSum.command := by
  refine ⟨⟨Control.nodeAppendPrepare_avoids,
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
  ⟨clear_avoids 851 (by decide), Control.expandCaller_avoids⟩

theorem representative_install_avoids : AvoidsCmd H QueryTupleVisitor.installRepresentative :=
  ⟨overwrite_avoids 838 859 (by decide) (by decide),
    avoids_compiled H _ (Factor.Head.overlay_avoids) _ _,
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
  Factor.head_avoids

theorem concrete_tuple_init_avoids : AvoidsCmd H QueryTupleInit.command :=
  tuple_init_avoids (QueryFactorKeptFrame.setup_avoids)

theorem head_prepare_avoids : AvoidsCmd H SignatureHeadPrepare.command :=
  Factor.Prepare.command_avoids

/-- The fixed visitor composes the actual two passes and all arithmetic
without any access to the retained interval744..767. -/
theorem visitor_avoids_of_loader
    (hload : AvoidsProgram H (SignatureHeadLoader.programFrom 843)) :
    AvoidsCmd H QueryVisitorProgram.visitor := by
  have hload' := SafeAvoids.call hload
  have hbaselineSafe := hload'.seq (SafeAvoids.intro representative_install_avoids)
  have hbaseline : AvoidsCmd H QueryVisitorProgram.baselineHead := by
    have hpack : ∃ c, c = QueryVisitorProgram.baselineHead ∧ SafeAvoids c := by
      refine ⟨_, ?_, hbaselineSafe⟩
      rw [QueryVisitorProgram.baselineHead]
    obtain ⟨_, rfl, hc⟩ := hpack
    exact hc.proof
  have hevaluateSafe := hload'.seq ((SafeAvoids.intro head_prepare_avoids).seq
    ((SafeAvoids.intro head_sum_avoids).seq (SafeAvoids.intro tuple_multiply_avoids)))
  have hevaluate : AvoidsCmd H QueryVisitorProgram.evaluateHead := by
    have hpack : ∃ c, c = QueryVisitorProgram.evaluateHead ∧ SafeAvoids c := by
      refine ⟨_, ?_, hevaluateSafe⟩
      rw [QueryVisitorProgram.evaluateHead, QueryVisitorProgram.loadHead,
        QueryVisitorProgram.evaluateLoadedHead]
    obtain ⟨_, rfl, hc⟩ := hpack
    exact hc.proof
  have hvisitor := (SafeAvoids.intro concrete_tuple_init_avoids).seq
    ((SafeAvoids.intro hbaseline).replay.seq
      ((SafeAvoids.intro hevaluate).replay.seq (SafeAvoids.intro tuple_end_avoids)))
  have hpack : ∃ c, c = QueryVisitorProgram.visitor ∧ SafeAvoids c := by
    refine ⟨_, ?_, hvisitor⟩
    rw [QueryVisitorProgram.visitor]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc.proof

theorem tuple_avoids_of_loader
    (hload : AvoidsProgram H (SignatureHeadLoader.programFrom 845))
    (hvisit : AvoidsCmd H QueryVisitorProgram.visitor) :
    AvoidsCmd H SignatureTupleComplete.command := by
  have htuple := (SafeAvoids.call hload).tupleController
    (SafeAvoids.intro candidate_avoids) (SafeAvoids.intro hvisit)
  have hpack : ∃ c, c = SignatureTupleComplete.command ∧ SafeAvoids c := by
    refine ⟨_, ?_, htuple⟩
    rw [SignatureTupleComplete.command, SignatureTupleComplete.routines,
      SignatureTupleLoader.loadHead, SignatureTupleLoader.headAddress]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc.proof


theorem visitor_avoids : AvoidsCmd H QueryVisitorProgram.visitor :=
  visitor_avoids_of_loader Loader.program843_avoids

theorem tuple_avoids : AvoidsCmd H SignatureTupleComplete.command :=
  tuple_avoids_of_loader Loader.program845_avoids visitor_avoids

theorem pair_callback_avoids : AvoidsCmd H QueryStreamProgram.pairCallback :=
  ⟨pair_start_avoids, tuple_avoids, commit_pair_avoids⟩

theorem pairs_avoids : AvoidsCmd H QueryStreamProgram.pairs := by
  apply QueryElementaryReplay.differenceCommand_avoids
  · intro i
    change ¬ (744 ≤ 832+i.val ∧ 832+i.val < 768)
    omega
  · exact pair_callback_avoids


theorem bootstrap_avoids : AvoidsCmd H QueryStreamProgram.bootstrapNode := by
  apply avoids_liftProgram
  exact Loader.bootstrap_avoids

theorem node_body_avoids : AvoidsCmd H QueryStreamProgram.nodeBody :=
  ⟨Control.beginNode_avoids,
    Control.nativeLayoutLoad_avoids, bootstrap_avoids,
    Control.setupCaller_avoids, pairs_avoids,
    Control.nodeFinish_avoids⟩

theorem nodes_avoids : AvoidsCmd H QueryStreamProgram.nodes := by
  refine ⟨Control.initializeNodes_avoids, ?_, node_body_avoids⟩
  change ¬ H 301
  decide

/-- The actual fixed conditioned query excludes the retained interval744..767,
including every invoked table and every peek. -/
theorem command_avoids : AvoidsCmd H QueryStreamProgram.command :=
  ⟨Control.prepareHigh_avoids, nodes_avoids,
    Control.reconstruction_avoids⟩

theorem program_avoids : AvoidsProgram H QueryStreamProgram.program :=
  avoids_compiled H _ command_avoids 330 323


/-- Actual instruction avoidance preserves a word at every trace prefix.
No successful-run or evaluator premise is required. -/
theorem trace_avoided {r s l steps : ℕ} (K : Fin s → Prop) [DecidablePred K]
    {p : Program r s l} (hp : AvoidsProgram K p) {a b : Cfg r s l}
    (ht : Trace p steps a b) (i : Fin s) (hi : K i) :
    b.stacks i = a.stacks i := by
  have ha : rebaseCfg K a.stacks a = a := by
    cases a with
    | mk pc regs words =>
        apply congrArg (fun ws => (⟨pc, regs, ws⟩ : Cfg r s l))
        funext j
        simp [rebaseStacks]
  have hr := trace_rebase K hp ht a.stacks
  rw [ha] at hr
  have hu := trace_same_length_unique ht hr
  have hw := congrArg (fun c => c.stacks i) hu
  simpa [rebaseCfg, rebaseStacks, hi] using hw

/-- The previously uncovered retained interval is unchanged inside every call. -/
theorem trace_interval {steps : ℕ}
    {a b : Cfg 40 896 (size QueryStreamProgram.command + 1)}
    (ht : Trace QueryStreamProgram.program steps a b)
    (i : Fin 896) (hlo : 744 ≤ i.val) (hhi : i.val < 768) :
    b.stacks i = a.stacks i := trace_avoided H program_avoids ht i ⟨hlo,hhi⟩

theorem eval_interval {steps : ℕ} {a b : State 40 896}
    (he : Eval QueryStreamProgram.command steps a b)
    (i : Fin 896) (hlo : 744 ≤ i.val) (hhi : i.val < 768) :
    b.stacks i = a.stacks i := trace_interval (compiled_halt_trace he 330 323) i hlo hhi

/-- Assemble the exact marked-return frame. The five source-word equalities
are endpoint facts supplied by the actual node and reconstruction executions;
all remaining retained words follow from the fixed code's access certificates. -/
theorem kept_frame {steps : ℕ} {a b : State 40 896}
    (he : Eval QueryStreamProgram.command steps a b)
    (hsource : ∀ i ∈ ([700,701,707,708,709] : List (Fin 896)), b.stacks i = a.stacks i)
    (i : Fin 896) (hi : HashMarkedReturn.kept i = true) : b.stacks i = a.stacks i := by
  have ht := compiled_halt_trace he 330 323
  simp only [HashMarkedReturn.kept, decide_eq_true_eq] at hi
  rcases hi with h | h | h | h | h | h | h | h | h | h
  · subst i
    exact trace_avoided _ QueryStreamFrames.program_avoids ht 320 (Or.inl rfl)
  · subst i
    exact trace_avoided _ QueryStreamFrames.program_avoids ht 322 (Or.inr rfl)
  · exact hsource i (by simp [h])
  · exact hsource i (by simp [h])
  · exact hsource i (by simp [h])
  · exact hsource i (by simp [h])
  · exact hsource i (by simp [h])
  · by_cases hlo : i.val < 768
    · exact trace_interval ht i h.1 hlo
    · exact trace_avoided _ QuerySelectorFrames.program_avoids ht i (by omega)
  · exact trace_avoided _ QuerySelectorFrames.program_avoids ht i (by omega)
  · subst i
    exact QueryTopFrame.eval_top he

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame
