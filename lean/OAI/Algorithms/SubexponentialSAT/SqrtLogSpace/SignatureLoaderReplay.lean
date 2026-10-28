import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayFootprint

/-! The actual bootstrap and head loader never inspect the two retained
collector tapes. This syntactic certificate includes peeks and all calls. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureLoaderReplay
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay

private theorem copyMany_avoids {s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s × Fin s)) (ht : ¬ H tmp)
    (hp : ∀ p∈ps,¬ H p.1 ∧ ¬ H p.2) : AvoidsCmd H (copyMany tmp ps) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨avoids_copyProgram H p.1 p.2 tmp 0 1 (hp p (by simp)).1
      (hp p (by simp)).2 ht,ih (fun q hq=>hp q (by simp [hq]))⟩

private theorem clearMany_avoids {s : ℕ} (H : Fin s → Prop) (ps : List (Fin s))
    (hp : ∀ p∈ps,¬ H p) : AvoidsCmd H (clearMany ps) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨avoids_clearProgram H p 0 1 (hp p (by simp)),ih (fun q hq=>hp q (by simp [hq]))⟩

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
    ¬ (workPort hs i=320 ∨ workPort hs i=322) := by
  intro h
  rcases h with h|h <;> have hv := congrArg Fin.val h <;>
    simp only [workPort,Fin.coe_ofNat_eq_mod,Nat.reduceMod] at hv <;> omega

private theorem stage_avoids {r s l : ℕ} (p : Program r s l) (reg : Fin r → Fin 16)
    (hs : s≤288) (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (hi : ∀ q∈ins,¬ (q.1=320 ∨ q.1=322))
    (ho : ∀ q∈outs,¬ (q.2=320 ∨ q.2=322)) :
    AvoidsCmd (fun i : Fin 768=>i=320 ∨ i=322) (stage p reg hs ins outs) := by
  let H := fun i : Fin 768=>i=320 ∨ i=322
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
    AvoidsCmd (fun i : Fin 768=>i=320 ∨ i=322) prepareHead := by
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · exact stage_avoids _ _ _ _ _ (by simp [headInputs]) (by simp [headOutputs])
  · exact stage_avoids _ _ _ _ _ (by simp [countInputs]) (by simp [countOutputs])
  · exact stage_avoids _ _ _ _ _ (by simp [scatterInputs]) (by simp [scatterOutputs])
  · exact stage_avoids _ _ _ _ _ (by simp [factorInputs]) (by simp [factorOutputs])

theorem bootstrap_avoids :
    AvoidsProgram (fun i : Fin 768=>i=320 ∨ i=322) SignatureHeadLoader.bootstrapProgram := by
  apply avoids_compiled
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · exact stage_avoids _ _ _ _ _ (by simp [addressInputs]) (by simp [addressOutputs])
  · exact stage_avoids _ _ _ _ _ (by simp [rowCountInputs]) (by simp [rowCountOutputs])
  · exact stage_avoids _ _ _ _ _ (by simp [cacheInputs]) (by simp [cacheOutputs])
  · exact clearMany_avoids _ retainedPorts (by simp [retainedPorts])
  · exact copyMany_avoids _ temporary retainedCopies (by decide) (by simp [retainedCopies])

theorem local_avoids :
    AvoidsProgram (fun i : Fin 768=>i=320 ∨ i=322) SignatureHeadLoader.localProgram := by
  apply avoids_compiled
  refine ⟨prepareHead_avoids,?_,?_,?_⟩
  · exact stage_avoids _ _ _ _ _ (by simp [SignatureHeadLoader.matrixInputs])
      (by simp [SignatureHeadLoader.rawOutputs])
  · exact stage_avoids _ _ _ _ _ (by simp [SignatureHeadLoader.shiftInputs])
      (by simp [SignatureHeadLoader.shiftOutputs])
  · exact avoids_clearProgram _ 669 0 1 (by decide)

theorem programFrom_avoids (src : Fin 896) (hs : src≠320) (ht : src≠322) :
    AvoidsProgram (fun i : Fin 896=>i=320 ∨ i=322) (SignatureHeadLoader.programFrom src) := by
  apply avoids_liftProgram
  apply avoids_compiled
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_⟩
  · exact clearMany_avoids _ [649,659,846,847] (by simp)
  · exact avoids_copyProgram _ src 649 659 0 1 (by simp [hs,ht]) (by decide) (by decide)
  · apply avoids_liftProgram
    change AvoidsProgram
      (fun i : Fin 768 => SignatureHeadLoader.lowStacks i = 320 ∨
        SignatureHeadLoader.lowStacks i = 322) SignatureHeadLoader.localProgram
    have hpred :
        (fun i : Fin 768 => SignatureHeadLoader.lowStacks i = 320 ∨
          SignatureHeadLoader.lowStacks i = 322) =
        (fun i : Fin 768 => i = 320 ∨ i = 322) := by
      funext i
      apply propext
      constructor
      · intro h
        rcases h with h | h
        · left
          apply Fin.ext
          have hv := congrArg Fin.val h
          change i.val = 320 at hv
          exact hv
        · right
          apply Fin.ext
          have hv := congrArg Fin.val h
          change i.val = 322 at hv
          exact hv
      · intro h
        rcases h with rfl | rfl
        · left
          apply Fin.ext
          rfl
        · right
          apply Fin.ext
          rfl
    rw [hpred]
    exact local_avoids
  · exact avoids_clearProgram _ 659 0 1 (by decide)
  · exact avoids_copyProgram _ 668 847 659 0 1 (by decide) (by decide) (by decide)
  · exact clearMany_avoids _ [668,669,846] (by simp)

theorem program843_avoids :
    AvoidsProgram (fun i : Fin 896=>i=320 ∨ i=322) (SignatureHeadLoader.programFrom 843) :=
  programFrom_avoids 843 (by decide) (by decide)

theorem program845_avoids :
    AvoidsProgram (fun i : Fin 896=>i=320 ∨ i=322) (SignatureHeadLoader.programFrom 845) :=
  programFrom_avoids 845 (by decide) (by decide)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureLoaderReplay
