import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterSetup
import OAI.Algorithms.SubexponentialSAT.SubexpHornerMachine

namespace OAI.Algorithms

/-! The concrete outer-CRT call to dense Horner evaluation, including all
argument copies, result transport, and cleanup. -/

namespace SubexponentialSAT.SubexpCRTOuterHorner

open BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing

def command : Code :=
  .seq (move 244 246) (.seq (copy 263 247) (.seq (copy 243 248)
    (.seq (SubexpHornerMachine.initializedCallAt registers hornerPorts)
      (.seq (move 200 264) (clearMany [247,250])))))

def budget (n B : ℕ) : ℕ :=
  SubexpHornerMachine.initializedBudget n B + 24 * B * n + 68 * B + 7 * n + 28

theorem budget_le (n B : ℕ) : budget n B ≤ 800000 * (n + 1) * (B + 1)^2 := by
  have hb := SubexpHornerMachine.initializedBudget_le n B
  have hs : 1 ≤ (B + 1)^2 := Nat.succ_le_of_lt (by positivity)
  have hB : B ≤ (B + 1)^2 := by nlinarith [Nat.zero_le (B^2)]
  have hn := Nat.mul_le_mul_left n hs
  have hnB := Nat.mul_le_mul_left n hB
  unfold budget
  nlinarith

/-- The caller retains the point and count, consumes its correction array,
and receives one flat coefficient. Every other stack is restored exactly. -/
theorem command_eval (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t x : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (P : List (Quad (Word (baseWidth p μ)))) (count : List Bool)
    (hc : count.length = P.length) (d : Data)
    (hP : d.stacks 244 = SubexpHornerMachine.encodePolynomial p μ P)
    (hx : d.stacks 263 = SubexpHornerMachine.flat x)
    (hcount : d.stacks 243 = count)
    (h318 : d.stacks 318 = []) (h319 : d.stacks 319 = []) (h264 : d.stacks 264 = [])
    (hlocal : ∀ i, d.stacks (hornerPorts i) =
      if i = 77 ∨ i = 78 ∨ i = 79 then [] else
        SubexpHornerControl.store
          (SubexpHornerMachine.initialWordsWithCount p μ M t x width P count) i) :
    ∃ n ≤ budget P.length (baseWidth p μ),
      ∃ (rf : Fin 16 → Bool) (output : Quad (Word (baseWidth p μ))),
        Eval command n d
          ⟨rf, Function.update (Function.update d.stacks 244 []) 264
            (SubexpHornerMachine.flat output)⟩ ∧
        SubexpHornerMachine.decode p μ c output =
          (PolynomialAlgorithm.denote (P.map (SubexpHornerMachine.decode p μ c))).eval
            (SubexpHornerMachine.decode p μ c x) := by
  have h246 : d.stacks 246 = [] := by simpa using hlocal 77
  have h247 : d.stacks 247 = [] := by simpa using hlocal 78
  have h248 : d.stacks 248 = [] := by simpa using hlocal 79
  have h200 : d.stacks 200 = [] := by
    simpa [SubexpHornerMachine.initialWordsWithCount, SubexpHornerMachine.initialWords,
      SubexpHornerControl.store] using hlocal 72
  have h250 : d.stacks 250 = [] := by
    simpa [SubexpHornerMachine.initialWordsWithCount, SubexpHornerMachine.initialWords,
      SubexpHornerControl.store] using hlocal 81
  let d1 := moved d 244 246
  have h1 := move_run d 244 246 (by decide) (by decide) (by decide) h319 h246
  let d2 := afterCopy d1 263 247 0 1
  have h2 := copy_run d1 263 247 (by decide) (by decide) (by decide)
    (by simpa [d1, moved] using h318)
  let d3 := afterCopy d2 243 248 0 1
  have h3 := copy_run d2 243 248 (by decide) (by decide) (by decide)
    (by simpa [d2, d1, afterCopy, StackRoutines.copyStacks, moved] using h318)
  have hprepared : d3.stacks =
      Function.update (Function.update (Function.update (Function.update d.stacks
        244 []) 246 (SubexpHornerMachine.encodePolynomial p μ P))
        247 (SubexpHornerMachine.flat x)) 248 count := by
    simp [d3, d2, d1, afterCopy, StackRoutines.copyStacks,
      hP, hx, hcount, h247, h248]
  have hav244 : ∀ i, hornerPorts i ≠ (244 : Fin 320) := by decide
  have hlocal3 : ∀ i, d3.stacks (hornerPorts i) =
      SubexpHornerControl.store
        (SubexpHornerMachine.initialWordsWithCount p μ M t x width P count) i := by
    intro i
    have hp77 : hornerPorts i = (246 : Fin 320) ↔ i = 77 := by
      rw [← hornerPorts_stream]
      exact hornerPorts.injective.eq_iff
    have hp78 : hornerPorts i = (247 : Fin 320) ↔ i = 78 := by
      rw [← hornerPorts_point]
      exact hornerPorts.injective.eq_iff
    have hp79 : hornerPorts i = (248 : Fin 320) ↔ i = 79 := by
      rw [← hornerPorts_count]
      exact hornerPorts.injective.eq_iff
    rw [hprepared]
    by_cases hi77 : i = 77
    · subst i
      simp [SubexpHornerControl.store, SubexpHornerMachine.initialWordsWithCount,
        SubexpHornerMachine.initialWords, SubexpHornerMachine.inputWords]
    · by_cases hi78 : i = 78
      · subst i
        simp [SubexpHornerControl.store, SubexpHornerMachine.initialWordsWithCount,
          SubexpHornerMachine.initialWords, SubexpHornerMachine.inputWords,
          SubexpHornerControl.readyWords, SubexpHornerMachine.baseWords]
      · by_cases hi79 : i = 79
        · subst i
          simp [SubexpHornerControl.store, SubexpHornerMachine.initialWordsWithCount]
        · simp [hp77, hp78, hp79, hav244,
            hlocal, hi77, hi78, hi79]
  obtain ⟨nh, rh, output, hnh, hh, hv⟩ :=
    SubexpHornerMachine.initialized_callAt_eval p μ M registers hornerPorts
      c t x ht width hw P count hc d3 hlocal3
  let d4 : Data := ⟨Function.extend registers rh d3.regs,
    Function.update (Function.update (Function.update (Function.update d3.stacks
      200 (SubexpHornerMachine.flat output)) 246 []) 248 [])
      250 (List.replicate (4 * baseWidth p μ) false)⟩
  have hhorner : Eval (SubexpHornerMachine.initializedCallAt registers hornerPorts)
      nh d3 d4 := by simpa only [d4, hornerPorts_output, hornerPorts_stream,
        hornerPorts_count, hornerPorts_blockWidth] using hh
  let d5 := moved d4 200 264
  have h5 := move_run d4 200 264 (by decide) (by decide) (by decide)
    (by simpa [d4, hprepared] using h319)
    (by simpa [d4, hprepared] using h264)
  let d6 := SubexpSetupStorage.clearManyState [247,250] d5
  have h6 := clearMany_run d5 [247,250]
  have hfinal : d6.stacks =
      Function.update (Function.update d.stacks 244 []) 264
        (SubexpHornerMachine.flat output) := by
    funext i
    by_cases hi244 : i = 244
    · subst i
      simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
        SubexpSetupStorage.clearState]
    · by_cases hi264 : i = 264
      · subst i
        simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
          SubexpSetupStorage.clearState]
      · by_cases hi200 : i = 200
        · subst i
          simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
            SubexpSetupStorage.clearState, h200]
        · by_cases hi246 : i = 246
          · subst i
            simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
              SubexpSetupStorage.clearState, h246]
          · by_cases hi247 : i = 247
            · subst i
              simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
                SubexpSetupStorage.clearState, h247]
            · by_cases hi248 : i = 248
              · subst i
                simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
                  SubexpSetupStorage.clearState, h248]
              · by_cases hi250 : i = 250
                · subst i
                  simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
                    SubexpSetupStorage.clearState, h250]
                · simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
                    SubexpSetupStorage.clearState,
                    hi244, hi264, hi200, hi246, hi247, hi248, hi250]
  have hrun := h1.seq (h2.seq (h3.seq (hhorner.seq (h5.seq h6))))
  have hout : d6 = ⟨d6.regs, Function.update (Function.update d.stacks 244 []) 264
      (SubexpHornerMachine.flat output)⟩ := state_ext rfl hfinal
  let total := 6 * (d.stacks 244).length + 6 +
    (7 * (d1.stacks 263).length + 5 +
      (7 * (d2.stacks 243).length + 5 +
        (nh + (6 * (d4.stacks 200).length + 6 +
          SubexpSetupStorage.clearManyCost [247,250] d5))))
  have hresult : Eval command total d d6 := hrun
  rw [hout] at hresult
  refine ⟨total, ?_, d6.regs, output, hresult, hv⟩
  simp [total, d5, d4, hprepared, d2, d1, afterCopy,
      StackRoutines.copyStacks, SubexpSetupStorage.clearManyCost,
      SubexpSetupStorage.clearState, hP, hx, hcount, hc,
      SubexpHornerMachine.encodePolynomial_length, SubexpQuarticFlatMul.flat_length,
      budget]
  nlinarith

end SubexponentialSAT.SubexpCRTOuterHorner

end OAI.Algorithms
