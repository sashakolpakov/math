import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramLayoutMasters
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram

/-! Actual elementary query commands never inspect the two retained marked
polynomial tapes. These certificates exclude peeks as well as writes. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryElementaryReplay

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open ProgramTapeReplay

private theorem isolated_avoids {r s l S : ℕ} (H : Fin S → Prop)
    (p : Program r s l) (register : Fin r → Fin 16) (stack : Fin s → Fin S)
    (tmp : Fin S) (ports : List (Fin S)) (inputs outputs : List (Fin S × Fin S))
    (ht : ¬ H tmp) (hp : ∀ i ∈ ports, ¬ H i)
    (hi : ∀ q ∈ inputs, ¬ H q.1 ∧ ¬ H q.2)
    (ho : ∀ q ∈ outputs, ¬ H q.1 ∧ ¬ H q.2)
    (hs : ∀ i, ¬ H (stack i)) :
    AvoidsCmd H (isolated p register stack tmp ports inputs outputs) := by
  refine ⟨?_, avoids_liftProgram_of_range H p register stack hs, ?_⟩
  · exact ⟨avoids_clearMany H [tmp] (by simpa using ht),
      avoids_clearMany H ports hp, avoids_resetMany H workRegisters,
      avoids_copyMany H tmp inputs ht hi⟩
  · refine ⟨avoids_clearMany H (outputs.map Prod.snd) ?_,
      avoids_copyMany H tmp outputs ht ho, avoids_clearMany H ports hp,
      avoids_resetMany H workRegisters⟩
    intro i h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact (ho q hq).2

private theorem bankClear_avoids {r s : ℕ} (H : Fin s → Prop)
    (tmp : Fin s) (value present : Fin r) (ports : List (Fin s))
    (ht : ¬ H tmp) (hp : ∀ i ∈ ports, ¬ H i) :
    AvoidsCmd H (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram H tmp value present ht
  | cons i ports ih =>
    exact ⟨avoids_clearProgram H i value present (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

/-- The paid unary false-count setup reads only its real local bank and
explicit copies; the marked polynomial tapes are absent from all accesses. -/
theorem countCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      PairNativeSetup.countCommand := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · intro i
    fin_cases i <;> decide

theorem setupCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      PairNativeSetup.setupCommand :=
  ⟨countCommand_avoids, avoids_clearMany _ _ (by norm_num [Fin.coe_ofNat_eq_mod]),
    avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide)⟩

theorem fillCommand_avoids (isE : Bool) :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      (PairNativeSetup.fillCommand isE) := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillInput, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillOutput, Fin.coe_ofNat_eq_mod]
  · intro i
    change ¬ (325+i.val=320 ∨ 325+i.val=322)
    omega

theorem expandCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      PairNativeSetup.expandCommand :=
  ⟨fillCommand_avoids true, fillCommand_avoids false⟩

theorem setupCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      PairNativeSetup.setupCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ setupCommand_avoids _ _)

theorem expandCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      PairNativeSetup.expandCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ expandCommand_avoids _ _)

theorem prepareHigh_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      HighQueryAdapter.prepareHigh := by
  refine ⟨⟨avoids_clearProgram _ _ _ _ (by decide),
    bankClear_avoids _ _ _ _ _ (by decide) (by norm_num [HighQueryAdapter.highChanged, Fin.coe_ofNat_eq_mod])⟩, ?_⟩
  apply avoids_liftProgram_of_range
  intro i
  fin_cases i <;> decide

theorem prepareHighProgram_avoids :
    AvoidsProgram (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      HighQueryAdapter.prepareHighProgram :=
  avoids_compiled _ _ prepareHigh_avoids _ _

/-- All four real controller tapes and the actual callback account for every
read or write, including strict-budget peeks in the pruned DFS. -/
theorem differenceCommand_avoids {r s : ℕ} (H : Fin s → Prop)
    (p : DifferencePairsProgram.Ports r s) (callback : Cmd r s)
    (hp : ∀ i, ¬ H (p.stack i)) (hc : AvoidsCmd H callback) :
    AvoidsCmd H (DifferencePairsProgram.command p callback) := by
  simp [DifferencePairsProgram.command, DifferencePairsProgram.body,
    DifferencePairsProgram.descend, DifferencePairsProgram.backtrack,
    DifferencePairsProgram.nextOutside, DifferencePairsProgram.finishLevel,
    DifferencePairsProgram.enter, DifferencePairsProgram.pushBit,
    DifferencePairsProgram.atoms, AvoidsCmd, AvoidsBase, AvoidsAtom, hp, hc]

theorem differenceProgram_avoids {r s : ℕ} (H : Fin s → Prop)
    (p : DifferencePairsProgram.Ports r s) (callback : Cmd r s)
    (hp : ∀ i, ¬ H (p.stack i)) (hc : AvoidsCmd H callback) :
    AvoidsProgram H (DifferencePairsProgram.program p callback) :=
  avoids_compiled _ _ (differenceCommand_avoids H p callback hp hc) _ _

/-- The original fourteen-copy loader uses only its real parked sources,
low destinations, and temporary684. -/
theorem layoutMasters_load_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val=320 ∨ i.val=322)
      LeafProgram.LayoutMasters.load := by
  apply avoids_liftProgram
  apply avoids_compiled
  apply avoids_copyMany
  · decide
  · intro q hq
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hq
    change ¬ (730+i.val=320 ∨ 730+i.val=322) ∧
      ¬ (128+i.val=320 ∨ 128+i.val=322)
    constructor <;> omega

/-- The literal paid loader command uses only its cleared workspace and the
original fourteen source/destination copies. -/
theorem layout_command_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      (.seq
        (liftCommand
          (clearMany (([684,660,665] : List (Fin 896)) ++
            LeafProgram.LayoutMasters.lowPorts.map (Fin.castAdd 128)))
          730 128 (Fin.castAdd 24) id)
        (liftCommand LeafProgram.LayoutMasters.load 730 128 id (Fin.castAdd 128))) := by
  constructor
  · apply avoids_liftProgram
    apply avoids_compiled
    apply avoids_clearMany
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl <;> decide
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp hj
      change ¬ (128+k.val=320 ∨ 128+k.val=322)
      omega
  · exact avoids_liftProgram _ _ _ _
      (avoids_compiled _ _ layoutMasters_load_avoids _ _)

/-- The certificate applies directly to the actual readiness-producing loader. -/
theorem nativeLayoutLoad_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322) NativeLayoutLoad.command :=
  layout_command_avoids

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryElementaryReplay
