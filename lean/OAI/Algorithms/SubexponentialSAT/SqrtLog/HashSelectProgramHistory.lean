import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramBounded

namespace OAI.Algorithms

/-! The fixed selector with an exact history invariant.  The paid mass
contract is required only at the literal states reached by the greedy
recurrence, rather than at arbitrary lists with the same length/support. -/
namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp

variable {r s : ℕ}

/-- Every callback is made at the exact prefix of this execution's history.
The program and charged budget are identical to `controller_eval_bounded`. -/
theorem controller_eval_history (p : ControllerPorts r s) (mass : Cmd r s)
    (frame : State r s) (score : Records → List Bool → List Bool)
    (valid : Records → List Bool → Prop) (B C cost : ℕ)
    (seed : List Bool) (rest initial : Records) (depth : List Bool) (a : State r s)
    (hmass : ∀ q < depth.length, ∀ state,
      ControllerReady p frame (seed :: rest)
        (iter (payloadNext score seed rest) q initial) state →
      MassSpec mass p.trial.core (afterCopyFamily p.trial state)
        (score (iter (payloadNext score seed rest) q initial))
        (valid (iter (payloadNext score seed rest) q initial)) B C cost)
    (hp : ∀ q < depth.length, ∀ bits ∈ seed :: rest,
      valid (iter (payloadNext score seed rest) q initial) bits ∧
        bits.length ≤ C ∧
        (score (iter (payloadNext score seed rest) q initial) bits).length = B)
    (ha : ControllerReady p frame (seed :: rest) initial a)
    (hd : a.stacks p.loop.counter = depth) :
    ∃ n ≤ controllerBudget B C cost (candidateEncoding (seed :: rest)).length
      (rest.length + 1) depth.length, ∃ b,
      ControllerReady p frame (seed :: rest)
        (iter (payloadNext score seed rest) depth.length initial) b ∧
      b.stacks p.loop.counter = [] ∧ b.regs p.loop.present = false ∧
      Eval (controller p mass) n a b := by
  let invariant := fun q rows state =>
    ControllerReady p frame (seed :: rest) rows state ∧
      rows = iter (payloadNext score seed rest) q initial
  have hspec : BoundedRoundSpec p.loop (round p.trial mass) (payloadNext score seed rest)
      invariant (roundBudget B C cost (candidateEncoding (seed :: rest)).length
        (rest.length + 1)) depth.length := by
    constructor
    · intro q rows state h
      exact ⟨ready_read p frame _ _ _ h.1, h.2⟩
    · intro q rows state hq hready hguard
      rcases hready with ⟨hready, rfl⟩
      obtain ⟨n, hn, b, ht, he, hr, hs, hg⟩ := round_eval_ready p.trial mass state
        (score (iter (payloadNext score seed rest) q initial))
        (valid (iter (payloadNext score seed rest) q initial)) B C cost
        (hmass q hq state hready) seed rest hready.1 hready.2.1 (hp q hq)
      refine ⟨n, ?_, b, ⟨?_, ?_⟩, ?_, ?_, ht⟩
      · simpa [hready.2.1] using hn
      · refine ⟨he, ?_, ?_, ?_, ?_⟩
        · exact (hs _ p.family_ne_rows p.trial.family_outside).trans hready.2.1
        · rw [best_scored] at hr
          simpa [payloadNext, candidateEncoding, scored, hready.2.2.1] using hr
        · intro i hi hc hout
          exact (hs i hi hout).trans (hready.2.2.2.1 i hi hc hout)
        · intro i hv hp hout
          exact (hg i hout).trans (hready.2.2.2.2 i hv hp hout)
      · exact (iter_succ_apply _ q initial).symm
      · exact hs _ (Ne.symm p.rows_ne_counter) p.counter_outside
      · exact (hg _ p.present_outside).trans hguard
  obtain ⟨n, hn, b, hb, hc, hg, ht⟩ := rounds_eval_bounded p.loop (round p.trial mass)
    (payloadNext score seed rest) invariant _ depth.length hspec 0 initial depth a
      (by simp) ⟨ha, rfl⟩ hd
  exact ⟨n, hn, b, hb.1, hc, hg, ht⟩

/-- Native trace for the same fixed instruction table and exact-history
callback contract, including its compiled halt. -/
theorem controllerProgram_trace_history (p : ControllerPorts r s) (mass : Cmd r s)
    (frame : State r s) (score : Records → List Bool → List Bool)
    (valid : Records → List Bool → Prop) (B C cost : ℕ)
    (seed : List Bool) (rest initial : Records) (depth : List Bool) (a : State r s)
    (hmass : ∀ q < depth.length, ∀ state,
      ControllerReady p frame (seed :: rest)
        (iter (payloadNext score seed rest) q initial) state →
      MassSpec mass p.trial.core (afterCopyFamily p.trial state)
        (score (iter (payloadNext score seed rest) q initial))
        (valid (iter (payloadNext score seed rest) q initial)) B C cost)
    (hp : ∀ q < depth.length, ∀ bits ∈ seed :: rest,
      valid (iter (payloadNext score seed rest) q initial) bits ∧
        bits.length ≤ C ∧
        (score (iter (payloadNext score seed rest) q initial) bits).length = B)
    (ha : ControllerReady p frame (seed :: rest) initial a)
    (hd : a.stacks p.loop.counter = depth) :
    ∃ n ≤ controllerBudget B C cost (candidateEncoding (seed :: rest)).length
      (rest.length + 1) depth.length + 1, ∃ b : State r s,
      b.stacks p.trial.rows = candidateEncoding
        (iter (payloadNext score seed rest) depth.length initial) ∧
      b.stacks p.loop.counter = [] ∧
      Trace (controllerProgram p mass) n
        (a.withPC (some (controllerProgram p mass).entry)) (b.withPC none) := by
  obtain ⟨n, hn, b, hb, hc, _, ht⟩ := controller_eval_history p mass frame score valid
    B C cost seed rest initial depth a hmass hp ha hd
  exact ⟨n + 1, Nat.add_le_add_right hn 1, b, hb.2.2.1, hc,
    compiled_halt_trace ht _ _⟩

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
