import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticDivisorScans

namespace OAI.Algorithms

/-! # The actual two-divisor-scan candidate predicate -/

namespace SubexponentialSAT.SubexpQuarticCandidateTest

open BitProgram StructuredCalls SubexpLiftRing
open SubexpQuarticProducerControl SubexpQuarticScanInvariant
open SubexpQuarticDivisorContracts SubexpQuarticDivisorScans

def finish (d : Data) : Data :=
  (StructuredProgram.Atom.set (12 : Fin 14) true).eval
    ((StructuredProgram.Atom.set (11 : Fin 14) false).eval
      ((StructuredProgram.Atom.band (13 : Fin 14) 13 10).eval d))

theorem finish_eval (d : Data) :
    Eval (.seq (atom (.band 13 13 10))
      (.seq (atom (.set 11 false)) (atom (.set 12 true)))) 3 d (finish d) := by
  exact Eval.seq (Eval.base (StructuredProgram.Eval.atom _ _))
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom _ _))
      (Eval.base (StructuredProgram.Eval.atom _ _)))

theorem finish_stacks (d : Data) : (finish d).stacks = d.stacks := rfl

theorem finish_flags (d : Data) :
    (finish d).regs 11 = false ∧ (finish d).regs 12 = true ∧
      (finish d).regs 13 = (d.regs 13 && d.regs 10) := by
  simp [finish, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr]

/-- Both exhaustive scans are actual finite-program executions. The first
result is saved in the outer iterator's result register while the quadratic
scan runs, then a Boolean instruction combines their results. -/
theorem test_eval (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (c : Fin 4 → ZMod p)
    (base : Data) (hb : Ready p M c base)
    (h25 : base.stacks 25 = ProgramEncoding.encodeRecords (linearRecords p))
    (h26 : base.stacks 26 = ProgramEncoding.encodeRecords (quadraticRecords p))
    (h27 : base.stacks 27 = []) (h23 : base.stacks 23 = []) (h24 : base.stacks 24 = []) :
    ∃ n next,
      n ≤ p * (51000 * (baseWidth p 1 + 1)^2 +
          24 * SubexpEnumerationPayload.scalarWidth p + 27) +
        p^2 * (76000 * (baseWidth p 1 + 1)^2 +
          48 * SubexpEnumerationPayload.scalarWidth p + 27) + 50 ∧
      Eval testCandidate n base next ∧ Ready p M c next ∧
      (∀ j : Fin 35, 25 ≤ j.val → next.stacks j = base.stacks j) ∧
      next.stacks 23 = [] ∧ next.stacks 24 = [] ∧
      next.regs 11 = false ∧ next.regs 12 = true ∧
      next.regs 13 = QuarticSearch.passes p c := by
  obtain ⟨n₁, a, hn₁, he₁, ha, hf₁, ha23, ha24, hlinear⟩ :=
    linear_scan p M c base hb h25 h27 h23 h24
  let b := (StructuredProgram.Atom.copy (13 : Fin 14) 10).eval a
  have hb' : Ready p M c b := ready_of_stacks_eq p M c a b ha rfl
  have hb26 : b.stacks 26 = ProgramEncoding.encodeRecords (quadraticRecords p) :=
    (hf₁.1 26 (by decide)).trans h26
  have hb27 : b.stacks 27 = [] := (hf₁.1 27 (by decide)).trans h27
  obtain ⟨n₂, q, hn₂, he₂, hq, hf₂, hq23, hq24, hquadratic⟩ :=
    quadratic_scan p M c b hb' hb26 hb27 ha23 ha24
  have hq13 : q.regs 13 = (QuarticSearch.elements p).all (QuarticSearch.linearPass p c) := by
    have h := hf₂.2 13 (by decide)
    change q.regs 13 = a.regs 10 at h
    exact h.trans hlinear
  let next := finish q
  have hflags := finish_flags q
  refine ⟨n₁ + (1 + (n₂ + 3)), next, by omega, ?_,
    ready_of_stacks_eq p M c q next hq rfl, ?_, hq23, hq24,
    hflags.1, hflags.2.1, ?_⟩
  · exact Eval.seq he₁ (Eval.seq (Eval.base (StructuredProgram.Eval.atom _ _))
      (Eval.seq he₂ (finish_eval q)))
  · intro j hj
    exact (hf₂.1 j hj).trans (hf₁.1 j hj)
  · change (finish q).regs 13 = _
    rw [hflags.2.2, hq13, hquadratic]
    rfl

end SubexponentialSAT.SubexpQuarticCandidateTest

end OAI.Algorithms
