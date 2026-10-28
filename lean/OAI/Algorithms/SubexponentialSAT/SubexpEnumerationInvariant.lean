import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationProgram

namespace OAI.Algorithms

/-!
# Invariant-bounded executions of the fixed interval enumerator

The callback need only terminate within its bound on states satisfying the
caller's invariant. The bound need not hold for arbitrary unbounded stacks.
Every callback invocation still supplies an actual structured execution, and
the conclusion is a bounded trace of the existing fixed finite program.
-/

namespace SubexponentialSAT.SubexpEnumerationInvariant

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms
open SubexponentialSAT.SubexpEnumerationProgram

variable {R S : ℕ}

/-- A bounded actual callback run on an invariant state. Both counters are
preserved exactly; the scratch stack is restored and the invariant retained. -/
abbrev BodyBound (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (P : Data R S → Prop) (C : ℕ) : Prop :=
  ∀ d : Data R S, P d → d.stacks p.scratch = [] →
    ∃ nb e, StructuredCalls.Eval body nb d e ∧ nb ≤ C ∧ P e ∧
      e.stacks p.current = d.stacks p.current ∧
      e.stacks p.remaining = d.stacks p.remaining ∧ e.stacks p.scratch = []

/-- The actual observed traversal, including its exact body-entry labels,
exists with the stated bound using only invariant-restricted callback runs. -/
theorem visits_exists_bounded (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (P : Data R S → Prop) (C : ℕ) (hbody : BodyBound p body P C)
    (hnext : ∀ d : Data R S, P d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.remaining) → P (nextState p d))
    (fuel L M : ℕ) :
    ∀ d : Data R S, P d → value (d.stacks p.remaining) = fuel →
      d.stacks p.scratch = [] →
      d.regs (p.register 2) = !(isZero (d.stacks p.remaining)) →
      (d.stacks p.current).length + fuel ≤ L →
      (d.stacks p.remaining).length ≤ M →
      ∃ n e, Visits p body (List.range' (value (d.stacks p.current)) fuel) n d e ∧
        P e ∧ n ≤ fuel * (C + 8 * L + 16 * M + 24) + 1 ∧
        value (e.stacks p.current) = value (d.stacks p.current) + fuel ∧
        value (e.stacks p.remaining) = 0 ∧ e.stacks p.scratch = [] := by
  induction fuel with
  | zero =>
      intro d hd hv hs hf hL hM
      have hz : isZero (d.stacks p.remaining) = true := (isZero_eq_true_iff _).2 hv
      refine ⟨1, d, ?_, hd, by simp, by simp, hv, hs⟩
      simpa using Visits.done d (by simpa [hz] using hf)
  | succ fuel ih =>
      intro d hd hv hs hf hL hM
      have hp : 0 < value (d.stacks p.remaining) := by omega
      have hz : isZero (d.stacks p.remaining) = false := (isZero_eq_false_iff _).2 hp
      have hf' : d.regs (p.register 2) = true := by simpa [hz] using hf
      obtain ⟨nb, e, he, hnb, hPe, hc, hr, heScratch⟩ := hbody d hd hs
      have hep : 0 < value (e.stacks p.remaining) := by simpa [hr] using hp
      have hnextcount : value ((nextState p e).stacks p.remaining) = fuel := by
        rw [nextState_remaining]
        have hdec := value_decrement hep
        have hevalue : value (e.stacks p.remaining) = fuel + 1 := by rw [hr, hv]
        omega
      have hcurrent : value ((nextState p e).stacks p.current) =
          value (d.stacks p.current) + 1 := by
        rw [nextState_current, value_increment, hc]
      have hnextL : ((nextState p e).stacks p.current).length + fuel ≤ L := by
        rw [nextState_current, hc]
        have hw := ripple_length_le true (e.stacks p.current)
        rw [hc] at hw
        omega
      have hnextM : ((nextState p e).stacks p.remaining).length ≤ M := by
        rw [nextState_remaining, decrement_length hep, hr]
        exact hM
      obtain ⟨nt, f, ht, hPf, hnt, hfc, hfr, hfs⟩ :=
        ih (nextState p e) (hnext e hPe heScratch hep) hnextcount
          (nextState_scratch ..) (nextState_flag ..) hnextL hnextM
      have hcost := advanceTestCost_le p e hep
      have heL : (e.stacks p.current).length ≤ L := by rw [hc]; omega
      have heM : (e.stacks p.remaining).length ≤ M := by simpa [hr] using hM
      refine ⟨(nb + advanceTestCost p e) + nt + 1, f, ?_, hPf, ?_, ?_, hfr, hfs⟩
      · simpa only [List.range'_succ, hcurrent] using
          Visits.step hf' he hc hr heScratch ht
      · rw [Nat.succ_mul]
        omega
      · rw [hcurrent] at hfc
        omega

/-- Whole-loop execution and cost from one invariant input. `P` may describe
size bounds and well-formedness of this particular input's reachable states. -/
theorem enumerate_bounded (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (P : Data R S → Prop) (C : ℕ) (hbody : BodyBound p body P C)
    (htest : ∀ d : Data R S, P d → d.stacks p.scratch = [] → P (testResult p d))
    (hnext : ∀ d : Data R S, P d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.remaining) → P (nextState p d))
    (d : Data R S) (hd : P d) (hs : d.stacks p.scratch = []) :
    ∃ n e, StructuredCalls.Eval (enumerate p body) n d e ∧ P e ∧
      n ≤ 8 * (d.stacks p.remaining).length + 8 + value (d.stacks p.remaining) *
        (C + 8 * ((d.stacks p.current).length + value (d.stacks p.remaining)) +
          16 * (d.stacks p.remaining).length + 24) ∧
      (∃ loopSteps, Visits p body
        (List.range' (value (d.stacks p.current)) (value (d.stacks p.remaining)))
        loopSteps (testResult p d) e) ∧
      value (e.stacks p.current) = value (d.stacks p.current) + value (d.stacks p.remaining) ∧
      value (e.stacks p.remaining) = 0 ∧ e.stacks p.scratch = [] := by
  have hst := testResult_stacks p d hs
  obtain ⟨n, e, he, hPe, hn, hc, hr, hscratch⟩ := visits_exists_bounded p body P C hbody hnext
    (value (d.stacks p.remaining))
    ((d.stacks p.current).length + value (d.stacks p.remaining))
    (d.stacks p.remaining).length
    (testResult p d) (htest d hd hs) (by rw [hst])
    (by rw [hst]; exact hs) (by rw [testResult_flag, hst])
    (by rw [hst]) (by rw [hst])
  refine ⟨(8 * (d.stacks p.remaining).length + 7) + n, e,
    .seq (test_eval p d hs) he.eval, hPe, ?_, ?_, ?_, hr, hscratch⟩
  · omega
  · exact ⟨n, by simpa only [hst] using he⟩
  · simpa only [hst] using hc

/-- The bound charges the generated final halt as well as every loop step.
The same finite source program is used for every invariant input. -/
theorem program_runsIn (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (P : Data R S → Prop) (C : ℕ) (hbody : BodyBound p body P C)
    (htest : ∀ d : Data R S, P d → d.stacks p.scratch = [] → P (testResult p d))
    (hnext : ∀ d : Data R S, P d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.remaining) → P (nextState p d))
    (d : Data R S) (hd : P d) (hs : d.stacks p.scratch = []) :
    ∃ e, P e ∧
      RunsIn (program p body)
        (8 * (d.stacks p.remaining).length + 9 + value (d.stacks p.remaining) *
          (C + 8 * ((d.stacks p.current).length + value (d.stacks p.remaining)) +
            16 * (d.stacks p.remaining).length + 24))
        (d.withPC (some (program p body).entry)) (e.withPC none) ∧
      value (e.stacks p.current) = value (d.stacks p.current) + value (d.stacks p.remaining) ∧
      value (e.stacks p.remaining) = 0 ∧ e.stacks p.scratch = [] := by
  obtain ⟨n, e, he, hPe, hn, hvisits, hc, hr, hscratch⟩ :=
    enumerate_bounded p body P C hbody htest hnext d hd hs
  exact ⟨e, hPe, ⟨n + 1, by omega, program_trace p body he⟩, hc, hr, hscratch⟩

/-- The invariant-restricted body hypothesis suffices all the way to an
actual bounded primitive trace; no global callback-cost hypothesis remains. -/
theorem program_primitive_runsIn (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (P : Data R S → Prop) (C : ℕ) (hbody : BodyBound p body P C)
    (htest : ∀ d : Data R S, P d → d.stacks p.scratch = [] → P (testResult p d))
    (hnext : ∀ d : Data R S, P d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.remaining) → P (nextState p d))
    (d : Data R S) (hd : P d) (hs : d.stacks p.scratch = []) :
    ∃ e, P e ∧
      Computation.RunsIn (BitProgram.primitive (program p body)).step
        (BitProgram.primitiveOverhead (program p body) *
          (8 * (d.stacks p.remaining).length + 9 + value (d.stacks p.remaining) *
            (C + 8 * ((d.stacks p.current).length + value (d.stacks p.remaining)) +
              16 * (d.stacks p.remaining).length + 24)))
        (BitProgram.primitiveCfg (program p body) (d.withPC (some (program p body).entry)))
        (BitProgram.primitiveCfg (program p body) (e.withPC none)) ∧
      value (e.stacks p.current) = value (d.stacks p.current) + value (d.stacks p.remaining) ∧
      value (e.stacks p.remaining) = 0 ∧ e.stacks p.scratch = [] := by
  obtain ⟨e, hPe, hr, hc, he, hs⟩ := program_runsIn p body P C hbody htest hnext d hd hs
  exact ⟨e, hPe, BitProgram.primitive_execution _ hr, hc, he, hs⟩

end SubexponentialSAT.SubexpEnumerationInvariant

end OAI.Algorithms
