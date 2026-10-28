import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram

namespace OAI.Algorithms

/-!+# Physical normalization of the retained frontend body

The local wrapper reserves stacks 0--15 for the closed normalizer, stack 16
for the retained body, and stack 17 for copying. It accepts arbitrary register
bits and empty local work stacks. The MainProgram procedure maps only the
body port into persistent storage, preserving every other persistent word.
-/

namespace SubexponentialSAT.SubexpFrontendNormalizationProgram

open BitProgram StructuredCalls

abbrev Data := State 16 18
abbrev formulaCode := SubexpNormalizationProgram.formulaCode

def Ready (d : Data) : Prop := ∀ i : Fin 18, i ≠ 16 → d.stacks i = []

def coreRegister (i : Fin 15) : Fin 16 := i.castAdd 1
def coreStack (i : Fin 16) : Fin 18 := i.castAdd 2

theorem coreRegister_injective : Function.Injective coreRegister := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 16 => i.val) h)

theorem coreStack_injective : Function.Injective coreStack := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 18 => i.val) h)

abbrev normalizeCall : Cmd 16 18 :=
  SubexpSetupStorage.invoke SubexpNormalizationProgram.program coreRegister coreStack

theorem normalizeCall_eval (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F)
    (hready : ∀ i : Fin 16, i ≠ 13 → d.stacks (coreStack i) = []) :
    ∃ n ≤ 3300 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval normalizeCall n d e ∧
      e.stacks 13 = formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F) ∧
      (∀ i : Fin 16, i ≠ 13 → e.stacks (coreStack i) = []) ∧
      e.stacks 16 = d.stacks 16 ∧ e.stacks 17 = d.stacks 17 := by
  let a := SubexpSetupStorage.project coreRegister coreStack d
  obtain ⟨b, hb, hbout, n, hn, ht⟩ :=
    SubexpNormalizationProgram.program_runsIn F a hsource hready
  let e := embedState coreRegister coreStack d b
  refine ⟨n, hn, e,
    SubexpSetupStorage.invoke_eval _ _ _ coreRegister_injective coreStack_injective d b ht,
    ?_, ?_, ?_, ?_⟩
  · exact (embedState_stack coreRegister coreStack d b coreStack_injective 13).trans hbout
  · intro i hi
    exact (embedState_stack coreRegister coreStack d b coreStack_injective i).trans (hb i hi)
  · apply embedState_stack_frame
    rintro ⟨i, hi⟩
    have hv := congrArg (fun i : Fin 18 => i.val) hi
    have := i.isLt
    simp only [coreStack, Fin.val_castAdd] at hv
    omega
  · apply embedState_stack_frame
    rintro ⟨i, hi⟩
    have hv := congrArg (fun i : Fin 18 => i.val) hi
    have := i.isLt
    simp only [coreStack, Fin.val_castAdd] at hv
    omega

abbrev command : Cmd 16 18 :=
  .seq (SubexpSetupStorage.copyCmd 16 13 17)
    (.seq normalizeCall
      (.seq (SubexpSetupStorage.clearCmd 16)
        (.seq (SubexpSetupStorage.copyCmd 13 16 17)
          (SubexpSetupStorage.clearCmd 13))))

theorem command_eval (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 16 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 3499 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval command n d e ∧ Ready e ∧
      e.stacks 16 = formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F) := by
  let a := SubexpSetupStorage.copyState 16 13 d
  have ha13 : a.stacks 13 = formulaCode F := by
    simp [a, SubexpSetupStorage.copyState, StackRoutines.copyStacks, hsource,
      hready 13 (by decide)]
  have haReady : ∀ i : Fin 16, i ≠ 13 → a.stacks (coreStack i) = [] := by
    intro i hi
    have hi13 : coreStack i ≠ 13 := fun h => hi (coreStack_injective h)
    have hi16 : coreStack i ≠ 16 := by
      intro h
      have hv := congrArg (fun i : Fin 18 => i.val) h
      have := i.isLt
      simp only [coreStack, Fin.val_castAdd] at hv
      omega
    exact (SubexpSetupStorage.copyState_frame 16 13 (coreStack i) d hi13).trans
      (hready (coreStack i) hi16)
  obtain ⟨m, hm, b, hnorm, hb13, hbready, hb16, hb17⟩ :=
    normalizeCall_eval F a ha13 haReady
  have hb16' : b.stacks 16 = formulaCode F := by
    simpa [a, SubexpSetupStorage.copyState, StackRoutines.copyStacks] using hb16.trans
      (show a.stacks 16 = formulaCode F by
        simpa [a, SubexpSetupStorage.copyState, StackRoutines.copyStacks] using hsource)
  have hb17' : b.stacks 17 = [] := by
    simpa [a, SubexpSetupStorage.copyState, StackRoutines.copyStacks] using hb17.trans
      (show a.stacks 17 = [] by
        simpa [a, SubexpSetupStorage.copyState, StackRoutines.copyStacks] using hready 17 (by decide))
  let c := SubexpSetupStorage.clearState 16 b
  let f := SubexpSetupStorage.copyState 13 16 c
  let e := SubexpSetupStorage.clearState 13 f
  have hc13 : c.stacks 13 = formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F) := by
    simpa [c, SubexpSetupStorage.clearState] using hb13
  have hc17 : c.stacks 17 = [] := by simpa [c, SubexpSetupStorage.clearState] using hb17'
  have hf13 : f.stacks 13 = formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F) := by
    simpa [f, SubexpSetupStorage.copyState, StackRoutines.copyStacks] using hc13
  have he16 : e.stacks 16 = formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F) := by
    simpa [e, f, SubexpSetupStorage.clearState, SubexpSetupStorage.copyState,
      StackRoutines.copyStacks, c] using hb13
  have heReady : Ready e := by
    intro i hi16
    by_cases hi13 : i = 13
    · subst i
      simp [e, SubexpSetupStorage.clearState]
    by_cases hi17 : i = 17
    · subst i
      simpa [e, f, c, SubexpSetupStorage.clearState, SubexpSetupStorage.copyState,
        StackRoutines.copyStacks] using hb17'
    have hi : i.val < 16 := by
      have hn16 : i.val ≠ 16 := fun h => hi16 (Fin.ext h)
      have hn17 : i.val ≠ 17 := fun h => hi17 (Fin.ext h)
      omega
    let j : Fin 16 := ⟨i.val, hi⟩
    have hj13 : j ≠ 13 := by
      intro h
      apply hi13
      exact Fin.ext (congrArg (fun j : Fin 16 => j.val) h)
    have hj : coreStack j = i := rfl
    have hb := hbready j hj13
    rw [hj] at hb
    simpa [e, f, c, SubexpSetupStorage.clearState, SubexpSetupStorage.copyState,
      StackRoutines.copyStacks, hi13, hi16] using hb
  let n := (7 * (d.stacks 16).length + 5) +
    (m + ((2 * (b.stacks 16).length + 3) +
      ((7 * (c.stacks 13).length + 5) + (2 * (f.stacks 13).length + 3))))
  refine ⟨n, ?_, e, ?_, heReady, he16⟩
  · have hlen := SubexpNormalizationProgram.normalize_length_le F
    dsimp [n]
    rw [hsource, hb16', hc13, hf13]
    nlinarith
  · exact (SubexpSetupStorage.copy_eval 16 13 17 d (by decide) (by decide) (by decide)
      (hready 17 (by decide))).seq
      (hnorm.seq ((SubexpSetupStorage.clear_eval 16 b).seq
        ((SubexpSetupStorage.copy_eval 13 16 17 c (by decide) (by decide) (by decide) hc17).seq
          (SubexpSetupStorage.clear_eval 13 f))))

def program := compiled command 16 16

theorem program_runsIn (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 16 = formulaCode F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧
      e.stacks 16 = formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F) ∧
      RunsIn program (3500 * ((formulaCode F).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hr, ho⟩ := command_eval F d hsource hready
  refine ⟨e, hr, ho, n + 1, ?_, compiled_halt_trace he 16 16⟩
  have hpos : 0 < ((formulaCode F).length + 1) ^ 2 := pow_pos (by omega) _
  omega

end SubexponentialSAT.SubexpFrontendNormalizationProgram

end OAI.Algorithms
