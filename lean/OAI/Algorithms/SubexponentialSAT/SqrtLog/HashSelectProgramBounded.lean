import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram

namespace OAI.Algorithms

/-! The uniform callback cost is required only for matrices smaller than the
certified final row count, rather than for arbitrarily long input matrices. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp

variable {r s : ℕ}

theorem controller_eval_bounded (p : ControllerPorts r s) (mass : Cmd r s)
    (frame : State r s) (score : Records → List Bool → List Bool)
    (valid : Records → List Bool → Prop) (B C cost : ℕ)
    (seed : List Bool) (rest rows : Records) (depth : List Bool) (a : State r s)
    (hmass : ∀ rows' a, rows'.length < rows.length + depth.length →
      rows' ⊆ (seed :: rest) ++ rows →
      ControllerReady p frame (seed :: rest) rows' a →
      MassSpec mass p.trial.core (afterCopyFamily p.trial a)
        (score rows') (valid rows') B C cost)
    (hp : ∀ rows', rows'.length < rows.length + depth.length →
      rows' ⊆ (seed :: rest) ++ rows →
      ∀ bits ∈ seed :: rest,
        valid rows' bits ∧ bits.length ≤ C ∧ (score rows' bits).length = B)
    (ha : ControllerReady p frame (seed :: rest) rows a)
    (hd : a.stacks p.loop.counter = depth) :
    ∃ n ≤ controllerBudget B C cost (candidateEncoding (seed :: rest)).length
      (rest.length + 1) depth.length, ∃ b,
      ControllerReady p frame (seed :: rest)
        (iter (payloadNext score seed rest) depth.length rows) b ∧
      b.stacks p.loop.counter = [] ∧ b.regs p.loop.present = false ∧
      Eval (controller p mass) n a b := by
  let invariant := fun q rows' a => ControllerReady p frame (seed :: rest) rows' a ∧
    rows'.length = rows.length + q ∧ rows' ⊆ (seed :: rest) ++ rows
  have hspec : BoundedRoundSpec p.loop (round p.trial mass) (payloadNext score seed rest)
      invariant (roundBudget B C cost (candidateEncoding (seed :: rest)).length
        (rest.length + 1)) depth.length := by
    constructor
    · intro q rows' a h
      exact ⟨ready_read p frame _ _ _ h.1, h.2⟩
    · intro q rows' a hq hready hguard
      have hlen : rows'.length < rows.length + depth.length := by
        have := hready.2.1; omega
      obtain ⟨n, hn, b, ht, he, hr, hs, hg⟩ := round_eval_ready p.trial mass a
        (score rows') (valid rows') B C cost (hmass rows' a hlen hready.2.2 hready.1)
        seed rest hready.1.1 hready.1.2.1 (hp rows' hlen hready.2.2)
      refine ⟨n, ?_, b, ⟨?_, ?_, ?_⟩, ?_, ?_, ht⟩
      · simpa [hready.1.2.1] using hn
      · refine ⟨he, ?_, ?_, ?_, ?_⟩
        · exact (hs _ p.family_ne_rows p.trial.family_outside).trans hready.1.2.1
        · rw [best_scored] at hr
          simpa [payloadNext, candidateEncoding, scored, hready.1.2.2.1] using hr
        · intro i hi hc hout
          exact (hs i hi hout).trans (hready.1.2.2.2.1 i hi hc hout)
        · intro i hv hp hout
          exact (hg i hout).trans (hready.1.2.2.2.2 i hv hp hout)
      · simp [payloadNext, hready.2.1, Nat.add_assoc]
      · intro bit hb
        rcases List.mem_cons.mp hb with h | h
        · subst bit
          exact List.mem_append.mpr (Or.inl (HashSelect.best_mem _ seed rest))
        · exact hready.2.2 h
      · exact hs _ (Ne.symm p.rows_ne_counter) p.counter_outside
      · exact (hg _ p.present_outside).trans hguard
  obtain ⟨n, hn, b, hb, hc, hg, ht⟩ := rounds_eval_bounded p.loop (round p.trial mass)
    (payloadNext score seed rest) invariant _ depth.length hspec 0 rows depth a
      (by simp) ⟨ha, by simp, fun _ h => List.mem_append.mpr (Or.inr h)⟩ hd
  exact ⟨n, hn, b, hb.1, hc, hg, ht⟩

theorem controllerProgram_trace_bounded (p : ControllerPorts r s) (mass : Cmd r s)
    (frame : State r s) (score : Records → List Bool → List Bool)
    (valid : Records → List Bool → Prop) (B C cost : ℕ)
    (seed : List Bool) (rest rows : Records) (depth : List Bool) (a : State r s)
    (hmass : ∀ rows' a, rows'.length < rows.length + depth.length →
      rows' ⊆ (seed :: rest) ++ rows →
      ControllerReady p frame (seed :: rest) rows' a →
      MassSpec mass p.trial.core (afterCopyFamily p.trial a)
        (score rows') (valid rows') B C cost)
    (hp : ∀ rows', rows'.length < rows.length + depth.length →
      rows' ⊆ (seed :: rest) ++ rows →
      ∀ bits ∈ seed :: rest,
        valid rows' bits ∧ bits.length ≤ C ∧ (score rows' bits).length = B)
    (ha : ControllerReady p frame (seed :: rest) rows a)
    (hd : a.stacks p.loop.counter = depth) :
    ∃ n ≤ controllerBudget B C cost (candidateEncoding (seed :: rest)).length
      (rest.length + 1) depth.length + 1, ∃ b : State r s,
      b.stacks p.trial.rows = candidateEncoding
        (iter (payloadNext score seed rest) depth.length rows) ∧
      b.stacks p.loop.counter = [] ∧
      Trace (controllerProgram p mass) n
        (a.withPC (some (controllerProgram p mass).entry)) (b.withPC none) := by
  obtain ⟨n, hn, b, hb, hc, _, ht⟩ := controller_eval_bounded p mass frame score valid
    B C cost seed rest rows depth a hmass hp ha hd
  exact ⟨n + 1, Nat.add_le_add_right hn 1, b, hb.2.2.1, hc,
    compiled_halt_trace ht _ _⟩

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
