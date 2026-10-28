import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationProgram

namespace OAI.Algorithms

/-!
# Indexed cost schedules for actual interval enumeration

The loop invariant is asserted at loop entries. In particular, a callback may
extend an accumulator for the current index before the controller increments
that index: the invariant need only hold again after that increment. Callback
termination and cost are required only on invariant states with positive fuel.
The conclusions are actual executions of the existing fixed finite program.
-/

namespace SubexponentialSAT.SubexpEnumerationSchedule

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms
open SubexponentialSAT.SubexpEnumerationProgram

variable {R S : ℕ}

/-- Local callback obligation for an indexed loop. Every witness contains an
actual callback execution, exact preservation of the reserved counters, and
the invariant at the next loop entry. No claim about arbitrary states is used. -/
abbrev BodyStep (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (Inv : Data R S → Prop) (cost : ℕ → ℕ) : Prop :=
  ∀ d : Data R S, Inv d → d.stacks p.scratch = [] →
    0 < value (d.stacks p.remaining) → d.regs (p.register 2) = true →
    ∃ nb e, StructuredCalls.Eval body nb d e ∧
      e.stacks p.current = d.stacks p.current ∧
      e.stacks p.remaining = d.stacks p.remaining ∧ e.stacks p.scratch = [] ∧
      Inv (nextState p e) ∧ nb ≤ cost (value (d.stacks p.current))

/-- Sum of the index-dependent callback bounds and every controller step. -/
def loopBudget (cost : ℕ → ℕ) (start fuel currentWidth remainingWidth : ℕ) : ℕ :=
  ((List.range' start fuel).map cost).sum +
    fuel * (8 * currentWidth + 16 * remainingWidth + 24) + 1

/-- A constant allowance is needed only on the visited interval. Values of the
cost function outside that interval do not affect the execution bound. -/
theorem loopBudget_le (cost : ℕ → ℕ) (start fuel L M C : ℕ)
    (hcost : ∀ i ∈ List.range' start fuel, cost i ≤ C) :
    loopBudget cost start fuel L M ≤ fuel * (C + 8 * L + 16 * M + 24) + 1 := by
  have hs := List.sum_le_length_nsmul ((List.range' start fuel).map cost) C (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hcost i hi)
  simp only [List.length_map, List.length_range', nsmul_eq_mul] at hs
  calc
    loopBudget cost start fuel L M ≤
        fuel * C + fuel * (8 * L + 16 * M + 24) + 1 := by
      exact Nat.add_le_add_right (Nat.add_le_add_right hs _) _
    _ = _ := by ring

/-- The exact consecutive-index traversal exists under a loop-entry invariant.
All callback costs are summed individually, not maximized over arbitrary data. -/
theorem visits_bounded (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (Inv : Data R S → Prop) (cost : ℕ → ℕ) (hbody : BodyStep p body Inv cost)
    (fuel L M : ℕ) :
    ∀ d : Data R S, Inv d → value (d.stacks p.remaining) = fuel →
      d.stacks p.scratch = [] →
      d.regs (p.register 2) = !(isZero (d.stacks p.remaining)) →
      (d.stacks p.current).length + fuel ≤ L →
      (d.stacks p.remaining).length ≤ M →
      ∃ n e, Visits p body (List.range' (value (d.stacks p.current)) fuel) n d e ∧
        Inv e ∧ n ≤ loopBudget cost (value (d.stacks p.current)) fuel L M ∧
        value (e.stacks p.current) = value (d.stacks p.current) + fuel ∧
        value (e.stacks p.remaining) = 0 ∧ e.stacks p.scratch = [] := by
  induction fuel with
  | zero =>
      intro d hd hv hs hf hL hM
      have hz : isZero (d.stacks p.remaining) = true := (isZero_eq_true_iff _).2 hv
      refine ⟨1, d, ?_, hd, by simp [loopBudget], by simp, hv, hs⟩
      simpa using Visits.done d (by simpa [hz] using hf)
  | succ fuel ih =>
      intro d hd hv hs hf hL hM
      have hp : 0 < value (d.stacks p.remaining) := by omega
      have hz : isZero (d.stacks p.remaining) = false := (isZero_eq_false_iff _).2 hp
      have hf' : d.regs (p.register 2) = true := by simpa [hz] using hf
      obtain ⟨nb, e, he, hc, hr, heScratch, hnextInv, hnb⟩ := hbody d hd hs hp hf'
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
      obtain ⟨nt, f, ht, hIf, hnt, hfc, hfr, hfs⟩ :=
        ih (nextState p e) hnextInv hnextcount
          (nextState_scratch ..) (nextState_flag ..) hnextL hnextM
      have hcost := advanceTestCost_le p e hep
      have heL : (e.stacks p.current).length ≤ L := by rw [hc]; omega
      have heM : (e.stacks p.remaining).length ≤ M := by simpa [hr] using hM
      refine ⟨(nb + advanceTestCost p e) + nt + 1, f, ?_, hIf, ?_, ?_, hfr, hfs⟩
      · simpa only [List.range'_succ, hcurrent] using
          Visits.step hf' he hc hr heScratch ht
      · simp only [loopBudget, hcurrent] at hnt
        simp only [loopBudget, List.range'_succ, List.map_cons, List.sum_cons,
          Nat.succ_mul fuel (8 * L + 16 * M + 24)]
        omega
      · rw [hcurrent] at hfc
        omega

/-- Full enumerator bound, including the initial zero test. The entry invariant
is required at the actual post-test state, so the test may change flag bits. -/
theorem enumerate_bounded (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (Inv : Data R S → Prop) (cost : ℕ → ℕ) (hbody : BodyStep p body Inv cost)
    (d : Data R S) (hd : Inv (testResult p d)) (hs : d.stacks p.scratch = []) :
    ∃ n e, StructuredCalls.Eval (enumerate p body) n d e ∧ Inv e ∧
      n ≤ 8 * (d.stacks p.remaining).length + 7 +
        loopBudget cost (value (d.stacks p.current)) (value (d.stacks p.remaining))
          ((d.stacks p.current).length + value (d.stacks p.remaining))
          (d.stacks p.remaining).length ∧
      (∃ loopSteps, Visits p body
        (List.range' (value (d.stacks p.current)) (value (d.stacks p.remaining)))
        loopSteps (testResult p d) e) ∧
      value (e.stacks p.current) = value (d.stacks p.current) + value (d.stacks p.remaining) ∧
      value (e.stacks p.remaining) = 0 ∧ e.stacks p.scratch = [] := by
  have hst := testResult_stacks p d hs
  obtain ⟨n, e, he, hIe, hn, hc, hr, hscratch⟩ := visits_bounded p body Inv cost hbody
    (value (d.stacks p.remaining))
    ((d.stacks p.current).length + value (d.stacks p.remaining))
    (d.stacks p.remaining).length (testResult p d) hd
    (by rw [hst]) (by rw [hst]; exact hs) (by rw [testResult_flag, hst])
    (by rw [hst]) (by rw [hst])
  refine ⟨(8 * (d.stacks p.remaining).length + 7) + n, e,
    .seq (test_eval p d hs) he.eval, hIe, ?_, ?_, ?_, hr, hscratch⟩
  · simpa only [hst] using Nat.add_le_add_left hn (8 * (d.stacks p.remaining).length + 7)
  · exact ⟨n, by simpa only [hst] using he⟩
  · simpa only [hst] using hc

/-- Instruction count including the initial test and final halt. -/
def programBudget (p : Ports R S) (cost : ℕ → ℕ) (d : Data R S) : ℕ :=
  8 * (d.stacks p.remaining).length + 8 +
    loopBudget cost (value (d.stacks p.current)) (value (d.stacks p.remaining))
      ((d.stacks p.current).length + value (d.stacks p.remaining))
      (d.stacks p.remaining).length

/-- The scheduled bound applies to the actual fixed instruction table. -/
theorem program_runsIn (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (Inv : Data R S → Prop) (cost : ℕ → ℕ) (hbody : BodyStep p body Inv cost)
    (d : Data R S) (hd : Inv (testResult p d)) (hs : d.stacks p.scratch = []) :
    ∃ e, Inv e ∧
      RunsIn (program p body) (programBudget p cost d)
        (d.withPC (some (program p body).entry)) (e.withPC none) ∧
      value (e.stacks p.current) = value (d.stacks p.current) + value (d.stacks p.remaining) ∧
      value (e.stacks p.remaining) = 0 ∧ e.stacks p.scratch = [] := by
  obtain ⟨n, e, he, hIe, hn, _, hc, hr, hscratch⟩ :=
    enumerate_bounded p body Inv cost hbody d hd hs
  refine ⟨e, hIe, ⟨n + 1, ?_, program_trace p body he⟩, hc, hr, hscratch⟩
  dsimp [programBudget]
  omega

/-- The same actual run is simulated by the checked primitive compiler.
The overhead depends only on the fixed program, never on the input values. -/
theorem program_primitive_runsIn (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (Inv : Data R S → Prop) (cost : ℕ → ℕ) (hbody : BodyStep p body Inv cost)
    (d : Data R S) (hd : Inv (testResult p d)) (hs : d.stacks p.scratch = []) :
    ∃ e, Inv e ∧
      Computation.RunsIn (BitProgram.primitive (program p body)).step
        (BitProgram.primitiveOverhead (program p body) * programBudget p cost d)
        (BitProgram.primitiveCfg (program p body) (d.withPC (some (program p body).entry)))
        (BitProgram.primitiveCfg (program p body) (e.withPC none)) ∧
      value (e.stacks p.current) = value (d.stacks p.current) + value (d.stacks p.remaining) ∧
      value (e.stacks p.remaining) = 0 ∧ e.stacks p.scratch = [] := by
  obtain ⟨e, hIe, hr, hc, he, hs⟩ := program_runsIn p body Inv cost hbody d hd hs
  exact ⟨e, hIe, BitProgram.primitive_execution _ hr, hc, he, hs⟩

end SubexponentialSAT.SubexpEnumerationSchedule

end OAI.Algorithms
