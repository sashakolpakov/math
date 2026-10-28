import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeTrialPrep
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeInitProgram

namespace OAI.Algorithms

/-!
# Finite-control prime trial enumeration

The trial body is the concrete binary division, zero scan, and Boolean update
from `SubexpPrimeTrialPrep`.  No semantic primality predicate is an instruction.
The divisor and remaining count are little-endian binary words on stacks 5 and
7; stack 9 retains the candidate and register 8 accumulates nondivisibility.
-/

namespace SubexponentialSAT.SubexpPrimeSearchProgram

open BitProgram StructuredProgram StructuredCalls
open SubexpPrimeProgram SubexpPrimeTrialPrep SubexpEnumerationProgram

abbrev State := StructuredProgram.State 9 10

def trialPorts : SubexpEnumerationProgram.Ports 9 10 where
  register := ⟨SubexpPrimeProgram.zeroRegister, SubexpPrimeProgram.zeroRegister_injective⟩
  current := 5
  remaining := 7
  scratch := 8
  current_ne_remaining := by decide
  current_ne_scratch := by decide
  remaining_ne_scratch := by decide

theorem trialFlag_frame (j : Fin 3) : trialPorts.register j ≠ 8 := by
  intro h
  exact flag_not_zeroRegister ⟨j, h⟩

abbrev trialScan : StructuredCalls.Cmd 9 10 :=
  SubexpEnumerationProgram.enumerate trialPorts SubexpPrimeTrialPrep.prepareAndTrial

theorem trialBody_total : BodyTotal trialPorts SubexpPrimeTrialPrep.prepareAndTrial := by
  intro a hs
  obtain ⟨n, b, he, ht, hf, hb⟩ := SubexpPrimeTrialPrep.prep_execution a
  refine ⟨n, b, he, ?_, ?_, ?_⟩
  · rw [hb]; rfl
  · rw [hb]; rfl
  · rw [hb]
    exact hs

theorem trialScan_execution (a : State) (hs : a.stacks 8 = []) :
    ∃ n b, StructuredCalls.Eval trialScan n a b ∧
      CounterPrograms.value (b.stacks 5) =
        CounterPrograms.value (a.stacks 5) + CounterPrograms.value (a.stacks 7) ∧
      CounterPrograms.value (b.stacks 7) = 0 ∧ b.stacks 8 = [] := by
  obtain ⟨n, b, he, hv, hc, hr, hsc⟩ :=
    SubexpEnumerationProgram.enumerate_correct trialPorts
      SubexpPrimeTrialPrep.prepareAndTrial trialBody_total a hs
  exact ⟨n, b, he, hc, hr, hsc⟩

theorem trialBody_stacks {n : ℕ} {a b : State}
    (h : StructuredCalls.Eval SubexpPrimeTrialPrep.prepareAndTrial n a b) :
    b.stacks = SubexpPrimeTrialPrep.resultStacks a := by
  obtain ⟨m, c, hc, ht, hf, hs⟩ := SubexpPrimeTrialPrep.prep_execution a
  rw [SubexpPrimeProgram.eval_result_unique h hc 9 0]
  exact hs

theorem trialBody_flag {n : ℕ} {a b : State}
    (h : StructuredCalls.Eval SubexpPrimeTrialPrep.prepareAndTrial n a b)
    (hp : 0 < CounterPrograms.value (a.stacks 5)) :
    b.regs 8 = (a.regs 8 && !(decide
      (CounterPrograms.value (a.stacks 9) % CounterPrograms.value (a.stacks 5) = 0))) := by
  obtain ⟨m, c, hc, ht, hf, hs⟩ := SubexpPrimeTrialPrep.prep_correct a
    (by simpa only [CounterPrograms.value_eq_toNat] using hp)
  have heq := SubexpPrimeProgram.eval_result_unique h hc 9 0
  apply Bool.eq_iff_iff.mpr
  rw [heq]
  simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    CounterPrograms.value_eq_toNat] using hf

def TrialInvariant (candidate : List Bool) (a : State) : Prop :=
  a.stacks 9 = candidate ∧ 2 ≤ CounterPrograms.value (a.stacks 5)

theorem trialBody_invariant {n : ℕ} {a b : State} {candidate : List Bool}
    (h : StructuredCalls.Eval SubexpPrimeTrialPrep.prepareAndTrial n a b)
    (ha : TrialInvariant candidate a) : TrialInvariant candidate b := by
  have hs := trialBody_stacks h
  constructor
  · rw [hs]; exact ha.1
  · rw [hs]; exact ha.2

theorem trialNext_invariant {candidate : List Bool} {a : State}
    (ha : TrialInvariant candidate a) : TrialInvariant candidate (nextState trialPorts a) := by
  constructor
  · rw [nextState_other_stack trialPorts a 9 (by decide) (by decide) (by decide)]
    exact ha.1
  · change 2 ≤ CounterPrograms.value ((nextState trialPorts a).stacks trialPorts.current)
    rw [nextState_current, CounterPrograms.value_increment]
    have h := ha.2
    change 2 ≤ CounterPrograms.value (a.stacks 5) + 1
    omega

/-- A closed execution theorem: every divisor in the supplied interval is
tested by the actual remainder routine. All program tables have fixed size. -/
theorem trialScan_correct (a : State) (hs : a.stacks 8 = [])
    (hstart : 2 ≤ CounterPrograms.value (a.stacks 5)) :
    ∃ n b, StructuredCalls.Eval trialScan n a b ∧
      b.regs 8 = (a.regs 8 && trialFactors (CounterPrograms.value (a.stacks 9))
        (CounterPrograms.value (a.stacks 5)) (CounterPrograms.value (a.stacks 7))) ∧
      b.stacks 9 = a.stacks 9 ∧
      CounterPrograms.value (b.stacks 5) =
        CounterPrograms.value (a.stacks 5) + CounterPrograms.value (a.stacks 7) ∧
      CounterPrograms.value (b.stacks 7) = 0 ∧ b.stacks 8 = [] := by
  obtain ⟨n, b, he, ⟨m, hv⟩, hc, hr, hsc⟩ :=
    SubexpEnumerationProgram.enumerate_correct trialPorts
      SubexpPrimeTrialPrep.prepareAndTrial trialBody_total a hs
  have htest := testResult_stacks trialPorts a hs
  have hP : TrialInvariant (a.stacks 9) (testResult trialPorts a) := by
    constructor
    · rw [htest]
    · rw [htest]; exact hstart
  have hfold := hv.flag_fold_of_invariant 8 trialFlag_frame
    (fun d => !(decide (CounterPrograms.value (a.stacks 9) % d = 0)))
    (TrialInvariant (a.stacks 9)) hP (fun nb x y hxy hx => by
      refine ⟨trialBody_invariant hxy hx, ?_⟩
      have hf := trialBody_flag hxy (by have := hx.2; omega)
      change y.regs 8 = (x.regs 8 && !(decide
        (CounterPrograms.value (a.stacks 9) % CounterPrograms.value (x.stacks 5) = 0)))
      rw [← hx.1]
      exact hf) (fun x hx => trialNext_invariant hx)
  refine ⟨n, b, he, ?_, hfold.1.1, hc, hr, hsc⟩
  have hf := hfold.2
  rw [testResult_other_register trialPorts a 8 trialFlag_frame] at hf
  simpa only [trialFactors_eq_all, trialPorts] using hf

def trialScanProgram := StructuredCalls.compiled trialScan 9 9

/-- Complete trial division after concrete data initialization: the flag
decides primality, including the empty divisor interval for candidate two. -/
theorem trialScan_prime_correct (a : State) (hs : a.stacks 8 = [])
    (hcurrent : CounterPrograms.value (a.stacks 5) = 2)
    (hremaining : CounterPrograms.value (a.stacks 7) = CounterPrograms.value (a.stacks 9) - 2)
    (hflag : a.regs 8 = true) (hcandidate : 2 ≤ CounterPrograms.value (a.stacks 9)) :
    ∃ n b, StructuredCalls.Eval trialScan n a b ∧
      (b.regs 8 = true ↔ Nat.Prime (CounterPrograms.value (a.stacks 9))) ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 8 = [] := by
  obtain ⟨n, b, he, hf, hcan, hcur, hrem, hsc⟩ :=
    trialScan_correct a hs (by omega)
  refine ⟨n, b, he, ?_, hcan, hsc⟩
  rw [hf, hflag, Bool.true_and, hcurrent, hremaining]
  simpa [SubexpPrimeProgram.trialPrime, hcandidate] using
    SubexpPrimeProgram.trialPrime_true_iff (CounterPrograms.value (a.stacks 9))

theorem trialScan_trace (a : State) (hs : a.stacks 8 = [])
    (hstart : 2 ≤ CounterPrograms.value (a.stacks 5)) :
    ∃ (n : ℕ) (b : State), BitProgram.Trace trialScanProgram (n + 1)
      (a.withPC (some trialScanProgram.entry)) (b.withPC none) ∧
      b.regs 8 = (a.regs 8 && trialFactors (CounterPrograms.value (a.stacks 9))
        (CounterPrograms.value (a.stacks 5)) (CounterPrograms.value (a.stacks 7))) := by
  obtain ⟨n, b, he, hf, hc, hcur, hrem, hsc⟩ := trialScan_correct a hs hstart
  exact ⟨n, b, StructuredCalls.compiled_halt_trace he 9 9, hf⟩

/-- The complete trial-division program includes all binary counter
initialization. Its instruction table is independent of the candidate. -/
abbrev primeTestCmd : StructuredCalls.Cmd 9 10 :=
  .seq SubexpPrimeInitProgram.command trialScan

def primeTestProgram := StructuredCalls.compiled primeTestCmd 9 9

/-- Total execution on every word, with the candidate preserved. Numerical
primality correctness below concerns candidates at least two. -/
theorem primeTest_execution (a : State) :
    ∃ n b, StructuredCalls.Eval primeTestCmd n a b ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 8 = [] := by
  have hi := SubexpPrimeInitProgram.initializer_execution a
  obtain ⟨n, b, he, hf, hcan, hcur, hrem, hsc⟩ :=
    trialScan_correct (SubexpPrimeInitProgram.result a)
      (SubexpPrimeInitProgram.result_scratch a)
      (by simp [SubexpPrimeInitProgram.result_divisor, CounterPrograms.value])
  refine ⟨SubexpPrimeInitProgram.executionTime a + n, b, hi.seq he, ?_, hsc⟩
  simpa only [SubexpPrimeInitProgram.result_candidate] using hcan

theorem primeTest_correct (a : State)
    (hcandidate : 2 ≤ CounterPrograms.value (a.stacks 9)) :
    ∃ n b, StructuredCalls.Eval primeTestCmd n a b ∧
      (b.regs 8 = true ↔ Nat.Prime (CounterPrograms.value (a.stacks 9))) ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 8 = [] := by
  obtain ⟨hi, ht, hfuel, hdiv, hflag, hscratch, hcandidateWord⟩ :=
    SubexpPrimeInitProgram.initializer_correct a hcandidate
  obtain ⟨n, b, he, hp, hcan, hsc⟩ :=
    trialScan_prime_correct (SubexpPrimeInitProgram.result a) hscratch
      (by simp [hdiv, CounterPrograms.value])
      (by simpa only [hcandidateWord] using hfuel) hflag
      (by simpa only [hcandidateWord] using hcandidate)
  refine ⟨SubexpPrimeInitProgram.executionTime a + n, b, hi.seq he, ?_, ?_, hsc⟩
  · simpa only [hcandidateWord] using hp
  · exact hcan.trans hcandidateWord

theorem primeTest_frame {a b : State} {n : ℕ}
    (h : StructuredCalls.Eval primeTestCmd n a b) :
    b.stacks 9 = a.stacks 9 ∧ b.stacks 8 = [] := by
  obtain ⟨m, c, hc, hcan, hs⟩ := primeTest_execution a
  rw [SubexpPrimeProgram.eval_result_unique h hc 9 9]
  exact ⟨hcan, hs⟩

theorem primeTest_post {a b : State} {n : ℕ}
    (h : StructuredCalls.Eval primeTestCmd n a b)
    (hcandidate : 2 ≤ CounterPrograms.value (a.stacks 9)) :
    (b.regs 8 = true ↔ Nat.Prime (CounterPrograms.value (a.stacks 9))) ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 8 = [] := by
  obtain ⟨m, c, hc, hp, hcan, hs⟩ := primeTest_correct a hcandidate
  rw [SubexpPrimeProgram.eval_result_unique h hc 9 9]
  exact ⟨hp, hcan, hs⟩

theorem primeTest_trace (a : State)
    (hcandidate : 2 ≤ CounterPrograms.value (a.stacks 9)) :
    ∃ (n : ℕ) (b : State), BitProgram.Trace primeTestProgram (n + 1)
      (a.withPC (some primeTestProgram.entry)) (b.withPC none) ∧
      (b.regs 8 = true ↔ Nat.Prime (CounterPrograms.value (a.stacks 9))) ∧
      b.stacks 9 = a.stacks 9 := by
  obtain ⟨n, b, he, hp, hcan, hs⟩ := primeTest_correct a hcandidate
  exact ⟨n, b, StructuredCalls.compiled_halt_trace he 9 9, hp, hcan⟩

end SubexponentialSAT.SubexpPrimeSearchProgram

end OAI.Algorithms
