import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeRuntime

namespace OAI.Algorithms

/-!
# Workspace bounds after a nonempty prime trial scan

For candidates at least three, the first actual divisibility trial clears the
old workspace. The final word-size bound therefore depends on the candidate,
not on the size of work words left by an earlier candidate test.
-/

namespace SubexponentialSAT.SubexpPrimeStorage

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms
open SubexponentialSAT.SubexpEnumerationProgram SubexponentialSAT.SubexpPrimeSearchProgram
open SubexponentialSAT.SubexpPrimeRuntime

abbrev State := StructuredProgram.State 9 10

theorem first_body_sizes {B L M n : ℕ} {a b : State}
    (he : StructuredCalls.Eval SubexpPrimeTrialPrep.prepareAndTrial n a b)
    (hB : (a.stacks 9).length ≤ B)
    (hL : (a.stacks 5).length + value (a.stacks 7) ≤ L)
    (hM : (a.stacks 7).length ≤ M) : TrialSizes B L M b := by
  have hs := trialBody_stacks he
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hs, SubexpPrimeTrialPrep.resultStacks] using hB
  · simpa [hs, SubexpPrimeTrialPrep.resultStacks] using hL
  · simpa [hs, SubexpPrimeTrialPrep.resultStacks] using hM
  · intro i h5 h7 h8 h9
    rw [hs]
    fin_cases i <;>
      simp_all [SubexpPrimeTrialPrep.resultStacks, ModularArithmetic.reduce_length]
    all_goals omega

theorem visits_preserve_sizes {B L M n : ℕ} {labels : List ℕ} {a b : State}
    (h : Visits trialPorts SubexpPrimeTrialPrep.prepareAndTrial labels n a b)
    (ha : TrialSizes B L M a) (hcount : value (a.stacks 7) = labels.length) :
    TrialSizes B L M b := by
  induction h with
  | done d hf => exact ha
  | @step d e f nb nt labels hf hb hc hr hs ht ih =>
      have hep : 0 < value (e.stacks 7) := by
        rw [show e.stacks 7 = d.stacks 7 from hr, hcount]
        simp
      have hecount : value (e.stacks 7) = labels.length + 1 := by
        rw [show e.stacks 7 = d.stacks 7 from hr, hcount]
        rfl
      have hncount : value ((nextState trialPorts e).stacks 7) = labels.length := by
        change value ((nextState trialPorts e).stacks trialPorts.remaining) = _
        rw [nextState_remaining]
        have hv := value_decrement hep
        change value (ripple false (e.stacks 7)) = _
        omega
      exact ih ((ha.after_body hb).after_next hep) hncount

/-- A positive remaining count guarantees a first real callback, which
establishes the workspace invariant without any initial workspace bound. -/
theorem visits_final_sizes {B L M n : ℕ} {labels : List ℕ} {a b : State}
    (h : Visits trialPorts SubexpPrimeTrialPrep.prepareAndTrial labels n a b)
    (hB : (a.stacks 9).length ≤ B)
    (hL : (a.stacks 5).length + value (a.stacks 7) ≤ L)
    (hM : (a.stacks 7).length ≤ M)
    (hcount : value (a.stacks 7) = labels.length) (hp : 0 < value (a.stacks 7)) :
    TrialSizes B L M b := by
  cases h with
  | done d hf => simp at hcount; omega
  | @step d e f nb nt labels hf hb hc hr hs ht =>
      have hep : 0 < value (e.stacks 7) := by
        simpa only [show e.stacks 7 = a.stacks 7 from hr] using hp
      have hecount : value (e.stacks 7) = labels.length + 1 := by
        rw [show e.stacks 7 = a.stacks 7 from hr, hcount]
        rfl
      have hncount : value ((nextState trialPorts e).stacks 7) = labels.length := by
        change value ((nextState trialPorts e).stacks trialPorts.remaining) = _
        rw [nextState_remaining]
        have hv := value_decrement hep
        change value (ripple false (e.stacks 7)) = _
        omega
      exact visits_preserve_sizes ht ((first_body_sizes hb hB hL hM).after_next hep) hncount

theorem all_words_tight {B L M : ℕ} {a : State} (h : TrialSizes B L M a)
    (hM : M ≤ B + L) (hs : a.stacks 8 = []) :
    ∀ i : Fin 10, (a.stacks i).length ≤ B + L := by
  intro i
  by_cases h5 : i = 5
  · subst i
    have := h.current
    omega
  by_cases h7 : i = 7
  · subst i
    exact h.remaining.trans hM
  by_cases h8 : i = 8
  · subst i
    simp [hs]
  by_cases h9 : i = 9
  · subst i
    exact h.candidate.trans (by omega)
  exact h.work i h5 h7 h8 h9

/-- Incoming work may be arbitrarily large. At least one actual trial clears
it, and later trials preserve this candidate-dependent bound. -/
theorem primeTest_final_width {a b : State} {n : ℕ}
    (he : StructuredCalls.Eval primeTestCmd n a b)
    (hcandidate : 3 ≤ value (a.stacks 9)) :
    ∀ i : Fin 10, (b.stacks i).length ≤ (a.stacks 9).length + value (a.stacks 9) := by
  let d := SubexpPrimeInitProgram.result a
  have hi := SubexpPrimeInitProgram.initializer_correct a (by omega)
  have hp0 : 0 < value (a.stacks 9) := by omega
  have hd0 := value_decrement hp0
  have hp1 : 0 < value (ripple false (a.stacks 9)) := by omega
  have hdM : (d.stacks 7).length ≤ (a.stacks 9).length := by
    dsimp only [d]
    rw [SubexpPrimeInitProgram.result_fuel, decrement_length hp1, decrement_length hp0]
  obtain ⟨t, e, ht, ⟨u, hv⟩, hc, hr, hscr⟩ :=
    SubexpEnumerationProgram.enumerate_correct trialPorts SubexpPrimeTrialPrep.prepareAndTrial
      trialBody_total d (SubexpPrimeInitProgram.result_scratch a)
  have hst := testResult_stacks trialPorts d (SubexpPrimeInitProgram.result_scratch a)
  have hfuel : value (d.stacks 7) = value (a.stacks 9) - 2 := hi.2.2.1
  have hL : ((testResult trialPorts d).stacks 5).length +
      value ((testResult trialPorts d).stacks 7) ≤ value (a.stacks 9) := by
    rw [hst, hfuel]
    dsimp only [d]
    rw [SubexpPrimeInitProgram.result_divisor]
    simp only [List.length_cons, List.length_nil]
    omega
  have hB : ((testResult trialPorts d).stacks 9).length ≤ (a.stacks 9).length := by
    rw [hst]
    dsimp only [d]
    rw [SubexpPrimeInitProgram.result_candidate]
  have hM : ((testResult trialPorts d).stacks 7).length ≤ (a.stacks 9).length := by
    simpa only [hst] using hdM
  have hcount : value ((testResult trialPorts d).stacks 7) =
      (List.range' (value (d.stacks trialPorts.current))
        (value (d.stacks trialPorts.remaining))).length := by
    simp only [hst, List.length_range']
    rfl
  have hp : 0 < value ((testResult trialPorts d).stacks 7) := by
    rw [hst, hfuel]
    omega
  have hfinal := visits_final_sizes hv hB hL hM hcount hp
  have hrun : StructuredCalls.Eval primeTestCmd (SubexpPrimeInitProgram.executionTime a + t) a e :=
    hi.1.seq ht
  have heq := SubexpPrimeProgram.eval_result_unique he hrun 9 9
  rw [heq]
  exact all_words_tight hfinal (by omega) hscr

end SubexponentialSAT.SubexpPrimeStorage

end OAI.Algorithms
