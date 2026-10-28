import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeCandidateProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeStorage

namespace OAI.Algorithms

/-! Actual cost and workspace bounds for the prime test as called by the
outer candidate search. The inner compiled halt is a charged return jump. -/

namespace SubexponentialSAT.SubexpPrimeCandidateRuntime

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms
open SubexponentialSAT.SubexpPrimeCandidateProgram SubexponentialSAT.SubexpPrimeRuntime

abbrev State := StructuredProgram.State 9 12

theorem candidateTest_bounded (a : State) (B : ℕ)
    (hB : ∀ i : Fin 10, (a.stacks (stackMap i)).length ≤ B)
    (hcandidate : 2 ≤ value (a.stacks 9)) :
    ∃ n b, StructuredCalls.Eval candidateTest n a b ∧
      n ≤ primeTestBound B (value (a.stacks 9)) + 1 ∧
      (b.regs 8 = true ↔ Nat.Prime (value (a.stacks 9))) ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 10 = a.stacks 10 ∧
      b.stacks 11 = a.stacks 11 ∧ b.stacks 8 = [] := by
  obtain ⟨n, b, he, hn, hp, hc, hs⟩ :=
    SubexpPrimeRuntime.primeTest_bounded (localState a) B hB hcandidate
  refine ⟨n + 1, install a b, candidateTest_refinement a b he,
    Nat.add_le_add_right hn 1, ?_, ?_, install_high a b 10 (by decide),
    install_high a b 11 (by decide), ?_⟩
  · change (b.regs 8 = true ↔ Nat.Prime (value (a.stacks 9))) at hp
    simpa only [install_regs] using hp
  · exact (install_low a b 9).trans hc
  · exact (install_low a b 8).trans hs

/-- A size bound is required only for the actual incoming state. -/
theorem candidateTest_steps_le {a b : State} {n : ℕ}
    (he : StructuredCalls.Eval candidateTest n a b) (B : ℕ)
    (hB : ∀ i : Fin 10, (a.stacks (stackMap i)).length ≤ B)
    (hcandidate : 2 ≤ value (a.stacks 9)) :
    n ≤ primeTestBound B (value (a.stacks 9)) + 1 := by
  obtain ⟨m, c, hc, hm, _⟩ := candidateTest_bounded a B hB hcandidate
  rw [SubexpPrimeProgram.eval_steps_unique he hc 9 9]
  exact hm

theorem candidateTest_steps_le_polynomial {a b : State} {n : ℕ}
    (he : StructuredCalls.Eval candidateTest n a b) (B : ℕ)
    (hB : ∀ i : Fin 10, (a.stacks (stackMap i)).length ≤ B)
    (hcandidate : 2 ≤ value (a.stacks 9)) :
    n ≤ 10000 * (B + value (a.stacks 9) + 3) ^ 3 + 1 :=
  (candidateTest_steps_le he B hB hcandidate).trans
    (Nat.add_le_add_right (primeTestBound_le _ _) 1)

/-- For the nonempty outer dyadic interval every candidate is at least three.
The inner work words then forget the size of previous dirty work storage. -/
theorem candidateTest_final_width {a b : State} {n : ℕ}
    (he : StructuredCalls.Eval candidateTest n a b)
    (hcandidate : 3 ≤ value (a.stacks 9)) :
    ∀ i : Fin 10, (b.stacks (stackMap i)).length ≤
      (a.stacks 9).length + value (a.stacks 9) := by
  obtain ⟨m, c, hc, hcan, hs⟩ := SubexpPrimeSearchProgram.primeTest_execution (localState a)
  have houter := candidateTest_refinement a c hc
  have heq := SubexpPrimeProgram.eval_result_unique he houter 9 9
  have hw := SubexpPrimeStorage.primeTest_final_width hc hcandidate
  intro i
  rw [heq, install_low]
  exact hw i

end SubexponentialSAT.SubexpPrimeCandidateRuntime

end OAI.Algorithms
