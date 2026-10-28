import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree

/-! Well-founded assembly of the actual fixed DFS while command.
The body obligation is the concrete visit theorem; no finite successful run,
termination oracle, derivation tree or precomputed visit list is assumed.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit
variable {n : ℕ}

/-- This intermediate invariant is instantiated by the concrete prepared frame
and the proved per-visit resource envelope, before the final endpoint. -/
theorem execute (k M : ℕ) (threshold : List Bool) (leaf : Code) (budget bound : ℕ)
    (I : Frontier n → Data → Prop) (hM : 2 ≤ M)
    (hboundary : ∀ s d, I s d → Boundary threshold s d)
    (hspace : ∀ s d, I s d → ∀ i, (d.stacks i).length ≤ bound)
    (hbody : ∀ (node : Node n) rest total d, I ⟨node :: rest, total⟩ d →
      ∃ next t, t ≤ budget ∧ ∃ e, BoundedEval (body k leaf) t d e bound ∧
        Transition k M ⟨node :: rest, total⟩ next ∧ I next e)
    (s : Frontier n) (d : Data) (hI : I s d) :
    ∃ visits t total e, t ≤ visits * (budget + 1) + 1 ∧
      BoundedEval (loop k leaf) t d e bound ∧
      Transitions k M visits s ⟨[], total⟩ ∧ I ⟨[], total⟩ e := by
  generalize hm : DFSCompletedTree.potential s = measure
  induction measure using Nat.strong_induction_on generalizing s d with
  | h measure ih =>
    rcases s with ⟨pending, total⟩
    cases pending with
    | nil =>
      have hf : d.regs 2 = false := by
        simpa using (hboundary ⟨[], total⟩ d hI).continue_flag
      refine ⟨0, 1, total, d, by simp, ⟨.while_false hf, ?_⟩, .refl _, hI⟩
      exact StructuredSpace.while_false_stack_bound (body k leaf) 2 d hf
        (hspace ⟨[], total⟩ d hI) (compiled (loop k leaf) 256 256)
        (siteAddress (loop k leaf)) (exitAddress (loop k leaf))
        (compiled_site (loop k leaf) 256 256)
    | cons node rest =>
      obtain ⟨next, tb, htb, afterBody, hb, transition, hnext⟩ :=
        hbody node rest total d hI
      have hlt : DFSCompletedTree.potential next < measure :=
        hm ▸ DFSCompletedTree.transition_potential_lt transition hM
      obtain ⟨visits, t, result, final, ht, he, transitions, hfinal⟩ :=
        ih _ hlt next afterBody hnext rfl
      have hf : d.regs 2 = true := by
        simpa using (hboundary ⟨node :: rest, total⟩ d hI).continue_flag
      refine ⟨visits + 1, tb + t + 1, result, final, ?_,
        ⟨.while_true hf hb.eval he.eval, ?_⟩, .cons transition transitions, hfinal⟩
      · simp only [Nat.add_mul, Nat.one_mul]
        omega
      · exact StructuredSpace.while_true_stack_bound hf hb.eval he.eval 256 256
          hb.space he.space (compiled (loop k leaf) 256 256)
          (siteAddress (loop k leaf)) (exitAddress (loop k leaf))
          (compiled_site (loop k leaf) 256 256)

/-- The exact completed count and sharp node budget refer to the same
measured while execution, whose uniform prefix bound is independent of visits. -/
theorem execute_sharp (k : ℕ) (σ : ℚ) (hk : 2 ≤ k) (hσ : 0 < σ)
    (threshold : List Bool) (leaf : Code) (budget bound : ℕ)
    (I : Frontier n → Data → Prop)
    (hboundary : ∀ s d, I s d → Boundary threshold s d)
    (hspace : ∀ s d, I s d → ∀ i, (d.stacks i).length ≤ bound)
    (hbody : ∀ (node : Node n) rest total d, I ⟨node :: rest, total⟩ d →
      ∃ next t, t ≤ budget ∧ ∃ e, BoundedEval (body k leaf) t d e bound ∧
        Transition k (SparseBudget.chooseForSigma k σ hσ) ⟨node :: rest, total⟩ next ∧ I next e)
    (F : RawCNF n) (d : Data) (hv : Valid k F) (hI : I ⟨[⟨F, 0⟩], 0⟩ d) :
    ∃ visits t e, t ≤ visits * (budget + 1) + 1 ∧
      BoundedEval (loop k leaf) t d e bound ∧
      Boundary (n := n) threshold ⟨[], rawCount F⟩ e ∧
      (visits : ℝ) ≤
        ((SparseCharging.depthConstant k (SparseBudget.chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
          (2 : ℝ) ^ ((σ : ℝ) * n) := by
  have hM := (SparseBudget.chooseM_spec k σ.num.natAbs σ.den
    (SparseBudget.rational_data σ hσ).1).1
  obtain ⟨visits, t, total, e, ht, he, transitions, hfinal⟩ :=
    execute k (SparseBudget.chooseForSigma k σ hσ) threshold leaf budget bound I hM
      hboundary hspace hbody ⟨[⟨F, 0⟩], 0⟩ d hI
  have hcount := transitions.finished_count
  refine ⟨visits, t, e, ht, he, ?_, ?_⟩
  · simpa only [hcount] using hboundary ⟨[], total⟩ e hfinal
  · exact DFSCompletedTree.completed_visits_bound k σ hk hσ hv transitions

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop
