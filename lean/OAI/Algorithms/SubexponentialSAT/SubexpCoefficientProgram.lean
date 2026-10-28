import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientServiceProgram
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientInterval

namespace OAI.Algorithms

/-! Closed coefficient construction from binary p, r, Q, and R. -/

namespace SubexponentialSAT.SubexpCoefficientProgram

open BitProgram StructuredCalls SubexpSetupStorage SubexpSetupBoundSpec
open SubexpCoefficientStaging Subexp

def finish : Code := .seq (copyCmd 48 49 63) (.seq (clearCmd 44) RegisterResetProgram.all)
def finished (a : Data) : Data := RegisterResetProgram.zeroed (clearState 44 (copyState 48 49 a))
def finishCost (a : Data) : ℕ := 7 * (a.stacks 48).length + 5 +
  ((2 * (a.stacks 44).length + 3) + 16)

theorem finish_eval (a : Data) (h63 : a.stacks 63 = []) :
    Eval finish (finishCost a) a (finished a) := by
  have hc := copy_eval (48 : Fin 64) 49 63 a (by decide) (by decide) (by decide) h63
  have he := hc.seq ((clear_eval 44 (copyState 48 49 a)).seq (RegisterResetProgram.all_eval _))
  simpa only [finish, finished, finishCost, copyState_frame 48 49 44 a (by decide)] using he

theorem finished_stacks (a : Data) (h49 : a.stacks 49 = []) (i : Fin 64) :
    (finished a).stacks i = if i = 44 then [] else if i = 49 then a.stacks 48 else a.stacks i := by
  simp [finished, RegisterResetProgram.zeroed, clearState, copyState_stack,
    Function.update_apply, h49]

def command : Code := .seq initializer.command (.seq SubexpCoefficientServiceProgram.command finish)
def program := compiled command 40 48
def afterInitBound (B : ℕ) : ℕ := B + initializerBound B
def wordBound (p r Q R B : ℕ) [Fact p.Prime] : ℕ :=
  SubexpCoefficientServiceProgram.wordBound p (SubexpIntervalStart.value r Q R) R (afterInitBound B)
def budget (p r Q R B : ℕ) [Fact p.Prime] : ℕ :=
  400 * (B + initializerBound B + 1) +
  SubexpCoefficientServiceProgram.budget p (SubexpIntervalStart.value r Q R) R (afterInitBound B) +
  10 * wordBound p r Q R B + 30

/-- All preparation and cleanup outside the actual coefficient search is
a fixed polynomial in the input-word bound and the two interval parameters. -/
def overhead (A R B : ℕ) : ℕ :=
  2138 * afterInitBound B +
    1738 * SubexpCoefficientInputs.innerBound (afterInitBound B) A R + 2239

theorem budget_eq (p r Q R B : ℕ) [Fact p.Prime] :
    budget p r Q R B = overhead (SubexpIntervalStart.value r Q R) R B +
      538 * CoefficientSearchService.budget p (SubexpIntervalStart.value r Q R) R := by
  unfold budget wordBound SubexpCoefficientServiceProgram.budget
    SubexpCoefficientServiceProgram.wordBound SubexpCoefficientInputs.budget
    overhead afterInitBound
  ring

def retained (i : Fin 64) : Prop := 40 ≤ i.val ∧ i.val ≤ 43 ∨ i = 48 ∨ i = 49

structure Result (a b : Data) (p r Q R : ℕ) [Fact p.Prime] where
  coefficients : Fin R → ZMod p
  output : b.stacks 48 = CoefficientSearchSemantics.encode p coefficients
  duplicate : b.stacks 49 = b.stacks 48
  correct : CoefficientNormalization.unnormalize (List.ofFn coefficients) =
    CoefficientSearch.coefficientsNat p (Subexp.TailInterval.intervalStart r Q R) R
  inputs : ∀ i : Fin 64, 40 ≤ i.val → i.val ≤ 43 → b.stacks i = a.stacks i
  empty : ∀ i : Fin 64, ¬ retained i → b.stacks i = []
  registers : ∀ i, b.regs i = false

theorem command_run (p r Q R B : ℕ) [Fact p.Prime] (hr : 0 < r)
    (h2 : (2 : ZMod p) ≠ 0) (a : Data) (ha : WordBound B a)
    (hpw : CounterPrograms.value (a.stacks 40) = p)
    (hrw : CounterPrograms.value (a.stacks 41) = r)
    (hQw : CounterPrograms.value (a.stacks 42) = Q)
    (hRw : CounterPrograms.value (a.stacks 43) = R) :
    ∃ t b, Eval command t a b ∧ t + 1 ≤ budget p r Q R B ∧
      WordBound (wordBound p r Q R B) b ∧ Nonempty (Result a b p r Q R) := by
  obtain ⟨ti, i, ei, hti, hwi, hi44, hif⟩ := initializer_run r Q R B hr a ha hrw hQw hRw
  have hi40 := hif 40 (by decide) (by decide) (by decide)
  have hi43 := hif 43 (by decide) (by decide) (by decide)
  obtain ⟨ts, s, v, es, hts, hws, hs48, hv, hsf, hsc, hsr⟩ :=
    SubexpCoefficientServiceProgram.command_run p (SubexpIntervalStart.value r Q R) R
      (afterInitBound B) h2 i hwi (by simpa only [hi40] using hpw)
      (by simpa only [hi43] using hRw) hi44
  have hs49 : s.stacks 49 = [] := hsc 49 (by decide)
  have hs63 : s.stacks 63 = [] := hsc 63 (by decide)
  have ef := finish_eval s hs63
  refine ⟨ti + (ts + finishCost s), finished s, ei.seq (es.seq ef), ?_, ?_, ?_⟩
  · have h48 := hws 48
    have h44 := hws 44
    unfold budget finishCost
    change _ ≤ 400 * (B + initializerBound B + 1) + _ + 10 * wordBound p r Q R B + 30
    change (s.stacks 48).length ≤ wordBound p r Q R B at h48
    change (s.stacks 44).length ≤ wordBound p r Q R B at h44
    omega
  · intro j
    rw [finished_stacks s hs49]
    split_ifs
    · simp
    · exact hws 48
    · exact hws j
  · refine ⟨⟨v, ?_, ?_, ?_, ?_, ?_, fun _ => rfl⟩⟩
    · rw [finished_stacks s hs49, ite_eq_right (by decide), ite_eq_right (by decide)]
      exact hs48
    · simp [finished_stacks s hs49]
    · simpa only [SubexpIntervalStart.value_eq_intervalStart r Q R hr] using hv
    · intro j hj40 hj43
      have hj44 : j ≠ 44 := by intro h; have := congrArg Fin.val h; norm_num at this; omega
      have hj49 : j ≠ 49 := by intro h; have := congrArg Fin.val h; norm_num at this; omega
      have hj63 : j ≠ 63 := by intro h; have := congrArg Fin.val h; norm_num at this; omega
      rw [finished_stacks s hs49, ite_eq_right hj44, ite_eq_right hj49]
      exact (hsf j hj40 (by omega)).trans (hif j (by omega) hj63 hj44)
    · intro j hj
      rw [finished_stacks s hs49]
      by_cases h44 : j = 44
      · simp [h44]
      have h49 : j ≠ 49 := fun h => hj (Or.inr (Or.inr h))
      rw [ite_eq_right h44, ite_eq_right h49]
      apply hsc j
      intro hret
      rcases hret with hrange | h48
      · apply hj
        left
        refine ⟨hrange.1, ?_⟩
        have hj44v : j.val ≠ 44 := fun h => h44 (Fin.ext h)
        omega
      · exact hj (Or.inr (Or.inl h48))

theorem program_run (p r Q R B : ℕ) [Fact p.Prime] (hr : 0 < r)
    (h2 : (2 : ZMod p) ≠ 0) (a : Data) (ha : WordBound B a)
    (hpw : CounterPrograms.value (a.stacks 40) = p)
    (hrw : CounterPrograms.value (a.stacks 41) = r)
    (hQw : CounterPrograms.value (a.stacks 42) = Q)
    (hRw : CounterPrograms.value (a.stacks 43) = R) :
    ∃ b, RunsIn program (budget p r Q R B) (a.withPC (some program.entry)) (b.withPC none) ∧
      WordBound (wordBound p r Q R B) b ∧ Nonempty (Result a b p r Q R) := by
  obtain ⟨t, b, he, ht, hw, hres⟩ := command_run p r Q R B hr h2 a ha hpw hrw hQw hRw
  exact ⟨b, ⟨t + 1, ht, compiled_halt_trace he 40 48⟩, hw, hres⟩

theorem primitive_run (p r Q R B : ℕ) [Fact p.Prime] (hr : 0 < r)
    (h2 : (2 : ZMod p) ≠ 0) (a : Data) (ha : WordBound B a)
    (hpw : CounterPrograms.value (a.stacks 40) = p)
    (hrw : CounterPrograms.value (a.stacks 41) = r)
    (hQw : CounterPrograms.value (a.stacks 42) = Q)
    (hRw : CounterPrograms.value (a.stacks 43) = R) :
    ∃ b, Computation.RunsIn (primitive program).step
        (primitiveOverhead program * budget p r Q R B)
        (primitiveCfg program (a.withPC (some program.entry)))
        (primitiveCfg program (b.withPC none)) ∧
      WordBound (wordBound p r Q R B) b ∧ Nonempty (Result a b p r Q R) := by
  obtain ⟨b, hb, hw, hres⟩ := program_run p r Q R B hr h2 a ha hpw hrw hQw hRw
  exact ⟨b, primitive_execution program hb, hw, hres⟩

end SubexponentialSAT.SubexpCoefficientProgram

end OAI.Algorithms
