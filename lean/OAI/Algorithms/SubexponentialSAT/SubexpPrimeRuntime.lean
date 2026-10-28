import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeSearchProgram
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationInvariant

namespace OAI.Algorithms

/-!
# Actual runtime of the fixed trial-division program

The bound is derived from the concrete preparation/division callback and an
invariant on the words stored by the interval controller. No callback oracle
or global all-configuration runtime premise is assumed.
-/

namespace SubexponentialSAT.SubexpPrimeRuntime

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms
open SubexponentialSAT.SubexpEnumerationProgram SubexponentialSAT.SubexpPrimeSearchProgram

abbrev State := StructuredProgram.State 9 10

/-- `L` bounds divisor width plus the number of remaining iterations. This
allows each increment to grow by one bit while preserving the same budget. -/
structure TrialSizes (B L M : ℕ) (a : State) : Prop where
  candidate : (a.stacks 9).length ≤ B
  current : (a.stacks 5).length + value (a.stacks 7) ≤ L
  remaining : (a.stacks 7).length ≤ M
  work : ∀ i : Fin 10, i ≠ 5 → i ≠ 7 → i ≠ 8 → i ≠ 9 →
    (a.stacks i).length ≤ B + L

def callbackBound (K : ℕ) : ℕ := 100 * (2 * K + 1) ^ 2 + 35 * K + 32

theorem TrialSizes.all_words {B L M : ℕ} {a : State} (h : TrialSizes B L M a)
    (hs : a.stacks 8 = []) : ∀ i : Fin 10, (a.stacks i).length ≤ B + L + M := by
  intro i
  by_cases h5 : i = 5
  · subst i
    have := h.current
    omega
  by_cases h7 : i = 7
  · subst i
    have := h.remaining
    omega
  by_cases h8 : i = 8
  · subst i
    simp [hs]
  by_cases h9 : i = 9
  · subst i
    have := h.candidate
    omega
  have := h.work i h5 h7 h8 h9
  omega

theorem TrialSizes.after_body {B L M n : ℕ} {a b : State}
    (h : TrialSizes B L M a)
    (he : StructuredCalls.Eval SubexpPrimeTrialPrep.prepareAndTrial n a b) :
    TrialSizes B L M b := by
  have hs := trialBody_stacks he
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hs, SubexpPrimeTrialPrep.resultStacks] using h.candidate
  · simpa [hs, SubexpPrimeTrialPrep.resultStacks] using h.current
  · simpa [hs, SubexpPrimeTrialPrep.resultStacks] using h.remaining
  · intro i h5 h7 h8 h9
    rw [hs]
    have hc := h.candidate
    have hd := h.current
    fin_cases i <;>
      simp_all [SubexpPrimeTrialPrep.resultStacks, ModularArithmetic.reduce_length]
    all_goals omega

theorem TrialSizes.after_test {B L M : ℕ} {a : State}
    (h : TrialSizes B L M a) (hs : a.stacks 8 = []) :
    TrialSizes B L M (testResult trialPorts a) := by
  have ht := testResult_stacks trialPorts a hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [ht] using h.candidate
  · simpa only [ht] using h.current
  · simpa only [ht] using h.remaining
  · simpa only [ht] using h.work

theorem TrialSizes.after_next {B L M : ℕ} {a : State}
    (h : TrialSizes B L M a) (hp : 0 < value (a.stacks 7)) :
    TrialSizes B L M (nextState trialPorts a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nextState_other_stack trialPorts a 9 (by decide) (by decide) (by decide)]
    exact h.candidate
  · change ((nextState trialPorts a).stacks trialPorts.current).length +
      value ((nextState trialPorts a).stacks trialPorts.remaining) ≤ L
    rw [nextState_current, nextState_remaining]
    have hl := ripple_length_le true (a.stacks 5)
    have hv := value_decrement hp
    have hc := h.current
    change (ripple true (a.stacks 5)).length + value (ripple false (a.stacks 7)) ≤ L
    omega
  · change ((nextState trialPorts a).stacks trialPorts.remaining).length ≤ M
    rw [nextState_remaining]
    simpa only [trialPorts, decrement_length hp] using h.remaining
  · intro i h5 h7 h8 h9
    rw [nextState_other_stack trialPorts a i h5 h7 h8]
    exact h.work i h5 h7 h8 h9

/-- The concrete callback discharges the invariant-local machine contract. -/
theorem bodyBound (B L M : ℕ) :
    SubexpEnumerationInvariant.BodyBound trialPorts
      SubexpPrimeTrialPrep.prepareAndTrial (TrialSizes B L M) (callbackBound (B + L + M)) := by
  intro a ha hs
  obtain ⟨n, b, he, hn, hf, hb⟩ := SubexpPrimeTrialPrep.prep_execution a
  have hcost := SubexpPrimeTrialPrep.trialBound_le_uniform a (B + L + M) (ha.all_words hs)
  refine ⟨n, b, he, hn.trans hcost, ha.after_body he, ?_, ?_, ?_⟩
  · rw [hb]; rfl
  · rw [hb]; rfl
  · rw [hb]; exact hs

/-- `N` is the actual number of divisors to visit; `B` bounds the initial
stored word widths. This is an explicit degree-three polynomial bound. -/
def scanBound (B N : ℕ) : ℕ :=
  8 * B + 8 + N * (callbackBound (3 * B + N) + 8 * (B + N) + 16 * B + 24)

theorem trialScan_bounded (a : State) (B : ℕ)
    (hB : ∀ i : Fin 10, (a.stacks i).length ≤ B) (hs : a.stacks 8 = []) :
    ∃ n b, StructuredCalls.Eval trialScan n a b ∧
      n ≤ scanBound B (value (a.stacks 7)) ∧
      (∀ i : Fin 10, (b.stacks i).length ≤ 3 * B + value (a.stacks 7)) ∧
      value (b.stacks 7) = 0 ∧ b.stacks 8 = [] := by
  let N := value (a.stacks 7)
  have ha : TrialSizes B (B + N) B a := by
    refine ⟨hB 9, ?_, hB 7, ?_⟩
    · exact Nat.add_le_add_right (hB 5) N
    · intro i _ _ _ _
      exact (hB i).trans (by omega)
  obtain ⟨n, b, he, hb, hn, hv, hc, hr, hscratch⟩ :=
    SubexpEnumerationInvariant.enumerate_bounded trialPorts
      SubexpPrimeTrialPrep.prepareAndTrial (TrialSizes B (B + N) B)
      (callbackBound (B + (B + N) + B)) (bodyBound B (B + N) B)
      (fun d hd hs => hd.after_test hs)
      (fun d hd _ hp => hd.after_next hp) a ha hs
  refine ⟨n, b, he, ?_, ?_, hr, hscratch⟩
  · have h5 := hB 5
    have h7 := hB 7
    have hK : B + (B + N) + B = 3 * B + N := by omega
    change n ≤ scanBound B N
    change n ≤ 8 * (a.stacks 7).length + 8 + N *
      (callbackBound (B + (B + N) + B) +
        8 * ((a.stacks 5).length + N) + 16 * (a.stacks 7).length + 24) at hn
    rw [hK] at hn
    exact hn.trans (by unfold scanBound; gcongr)
  · intro i
    have hi := hb.all_words hscratch i
    omega

theorem initializer_width (a : State) (B : ℕ)
    (hB : ∀ i : Fin 10, (a.stacks i).length ≤ B) :
    ∀ i : Fin 10, ((SubexpPrimeInitProgram.result a).stacks i).length ≤ B + 2 := by
  intro i
  by_cases h1 : i = 1
  · subst i
    simp
  by_cases h5 : i = 5
  · subst i
    simp
  by_cases h7 : i = 7
  · subst i
    rw [SubexpPrimeInitProgram.result_fuel]
    have h0 := hB 9
    have h1 := ripple_length_le false (a.stacks 9)
    have h2 := ripple_length_le false (ripple false (a.stacks 9))
    omega
  by_cases h8 : i = 8
  · subst i
    simp
  rw [SubexpPrimeInitProgram.result_frame a i h1 h5 h7 h8]
  exact (hB i).trans (by omega)

def primeTestBound (B N : ℕ) : ℕ := 31 * B + 46 + scanBound (B + 2) (N - 2)

private theorem le_square (X : ℕ) (hX : 1 ≤ X) : X ≤ X ^ 2 := by
  calc
    X = X * 1 := by omega
    _ ≤ X * X := Nat.mul_le_mul_left X hX
    _ = X ^ 2 := by ring

theorem callbackBound_le (K X : ℕ) (hX : 1 ≤ X) (hK : K ≤ 4 * X) :
    callbackBound K ≤ 8300 * X ^ 2 := by
  have hsquare : (2 * K + 1) ^ 2 ≤ (9 * X) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hs := le_square X hX
  unfold callbackBound
  nlinarith

/-- A fixed-degree polynomial in the input word bound and numeric candidate. -/
theorem primeTestBound_le (B N : ℕ) :
    primeTestBound B N ≤ 10000 * (B + N + 3) ^ 3 := by
  let X := B + N + 3
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hB : B + 2 ≤ X := by dsimp [X]; omega
  have hN : N - 2 ≤ X := by dsimp [X]; omega
  have hs := le_square X hX
  have hc := callbackBound_le (3 * (B + 2) + (N - 2)) X hX (by omega)
  have hinner : callbackBound (3 * (B + 2) + (N - 2)) +
      8 * (B + 2 + (N - 2)) + 16 * (B + 2) + 24 ≤ 8400 * X ^ 2 := by
    omega
  have hprod := Nat.mul_le_mul hN hinner
  have hcube : X ≤ X ^ 3 := by
    calc
      X ≤ X ^ 2 := hs
      _ = X ^ 2 * 1 := by omega
      _ ≤ X ^ 2 * X := Nat.mul_le_mul_left (X ^ 2) hX
      _ = X ^ 3 := by ring
  have hprefix : 31 * B + 46 + 8 * (B + 2) + 8 ≤ 100 * X := by
    dsimp [X]
    omega
  change primeTestBound B N ≤ 10000 * X ^ 3
  unfold primeTestBound scanBound
  nlinarith

/-- Initialization and every trial are charged. The candidate may carry
leading zeroes and the incoming work stacks may be nonempty. -/
theorem primeTest_bounded (a : State) (B : ℕ)
    (hB : ∀ i : Fin 10, (a.stacks i).length ≤ B)
    (hcandidate : 2 ≤ value (a.stacks 9)) :
    ∃ n b, StructuredCalls.Eval primeTestCmd n a b ∧
      n ≤ primeTestBound B (value (a.stacks 9)) ∧
      (b.regs 8 = true ↔ Nat.Prime (value (a.stacks 9))) ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 8 = [] := by
  have hi := SubexpPrimeInitProgram.initializer_correct a hcandidate
  obtain ⟨n, b, he, hn, hw, hr, hs⟩ :=
    trialScan_bounded (SubexpPrimeInitProgram.result a) (B + 2)
      (initializer_width a B hB) (SubexpPrimeInitProgram.result_scratch a)
  have hrun : StructuredCalls.Eval primeTestCmd (SubexpPrimeInitProgram.executionTime a + n) a b :=
    hi.1.seq he
  have hpost := primeTest_post hrun hcandidate
  refine ⟨SubexpPrimeInitProgram.executionTime a + n, b, hrun, ?_, hpost⟩
  rw [hi.2.2.1] at hn
  have ht := SubexpPrimeInitProgram.executionTime_le a
  have h1 := hB 1
  have h5 := hB 5
  have h7 := hB 7
  have h8 := hB 8
  have h9 := hB 9
  unfold SubexpPrimeInitProgram.timeBound at ht
  unfold primeTestBound
  omega

/-- The bit-program trace contains the same computation plus the final halt. -/
theorem primeTest_runsIn (a : State) (B : ℕ)
    (hB : ∀ i : Fin 10, (a.stacks i).length ≤ B)
    (hcandidate : 2 ≤ value (a.stacks 9)) :
    ∃ b : State, RunsIn primeTestProgram (primeTestBound B (value (a.stacks 9)) + 1)
      (a.withPC (some primeTestProgram.entry)) (b.withPC none) ∧
      (b.regs 8 = true ↔ Nat.Prime (value (a.stacks 9))) ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 8 = [] := by
  obtain ⟨n, b, he, hn, hp, hc, hs⟩ := primeTest_bounded a B hB hcandidate
  exact ⟨b, ⟨n + 1, Nat.add_le_add_right hn 1,
    StructuredCalls.compiled_halt_trace he 9 9⟩, hp, hc, hs⟩

theorem primeTest_primitive_runsIn (a : State) (B : ℕ)
    (hB : ∀ i : Fin 10, (a.stacks i).length ≤ B)
    (hcandidate : 2 ≤ value (a.stacks 9)) :
    ∃ b : State, Computation.RunsIn (BitProgram.primitive primeTestProgram).step
      (BitProgram.primitiveOverhead primeTestProgram * (primeTestBound B (value (a.stacks 9)) + 1))
      (BitProgram.primitiveCfg primeTestProgram (a.withPC (some primeTestProgram.entry)))
      (BitProgram.primitiveCfg primeTestProgram (b.withPC none)) ∧
      (b.regs 8 = true ↔ Nat.Prime (value (a.stacks 9))) ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 8 = [] := by
  obtain ⟨b, hr, hp, hc, hs⟩ := primeTest_runsIn a B hB hcandidate
  exact ⟨b, BitProgram.primitive_execution _ hr, hp, hc, hs⟩

/-- Exact-count determinism transfers the proved bound to any occurrence
of this concrete command in a larger execution. -/
theorem primeTest_steps_le {a b : State} {n : ℕ}
    (he : StructuredCalls.Eval primeTestCmd n a b) (B : ℕ)
    (hB : ∀ i : Fin 10, (a.stacks i).length ≤ B)
    (hcandidate : 2 ≤ value (a.stacks 9)) :
    n ≤ primeTestBound B (value (a.stacks 9)) := by
  obtain ⟨m, c, hc, hm, _⟩ := primeTest_bounded a B hB hcandidate
  rw [SubexpPrimeProgram.eval_steps_unique he hc 9 9]
  exact hm

theorem primeTest_steps_le_polynomial {a b : State} {n : ℕ}
    (he : StructuredCalls.Eval primeTestCmd n a b) (B : ℕ)
    (hB : ∀ i : Fin 10, (a.stacks i).length ≤ B)
    (hcandidate : 2 ≤ value (a.stacks 9)) :
    n ≤ 10000 * (B + value (a.stacks 9) + 3) ^ 3 :=
  (primeTest_steps_le he B hB hcandidate).trans (primeTestBound_le _ _)

end SubexponentialSAT.SubexpPrimeRuntime

end OAI.Algorithms
