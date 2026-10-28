import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteSpecTarget

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open Polynomial
noncomputable section

variable {r Q n d : ℕ}

theorem specTarget_degree_le (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (k factors : ℕ)
    (hwidth : ∀ clause∈q.source,clause.length ≤ k) (hfactors : q.rows.length ≤ factors) :
    (specTarget q H high).natDegree ≤ k*q.p.R*(2*factors+3*(q.p.t-1)+1) := by
  unfold specTarget
  rw [decodedHashes_lifted]
  have hm : q.markedClause.length ≤ k := by
    unfold Factor.Spec.markedClause
    by_cases h : q.mark < q.source.length
    · rw [List.getElem?_eq_getElem h,Option.getD_some]
      exact hwidth _ (List.getElem_mem h)
    · rw [List.getElem?_eq_none (by omega)]
      simp
  have h := NodeSemantics.branch_target_degree H high (completedRows q.p q.ps q.packing H)
    q.p.t k q.p.R (completedRows_degree q.p q.ps q.packing H) _
    (NodeSemantics.codeDigits_degree q.ctx (q.p.model.base q.p.t) q.code)
    (NodeSemantics.liftedHashes q.p.model q.p.t (sourceHashes q)) q.marked q.markedClause
    (NodeSemantics.liftedHashes_width q.p.model q.p.t k _ (sourceHashes_width q k hwidth)) hm
  apply h.trans
  unfold Reconstruction.markedDegreeBound
  simp only [NodeSemantics.liftedHashes,List.length_map,sourceHashes_length]
  gcongr

theorem specTarget_degree_of_budget (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (k factors : ℕ)
    (hwidth : ∀ clause∈q.source,clause.length ≤ k) (hfactors : q.rows.length ≤ factors)
    (hbudget : k*q.p.R*(2*factors+3*(q.p.t-1)+1) < Q*q.J) :
    (specTarget q H high).natDegree < Q*q.J :=
  (specTarget_degree_le q H high k factors hwidth hfactors).trans_lt hbudget

theorem specTarget_count_bound (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (m : ℕ) (hm : 1 ≤ m) :
    NodeSemantics.ternaryFixedHighCount H high (sourceHashes q) q.marked q.markedClause ≤ m*2^n := by
  rw [←NodeSemantics.fixedHighCount_lifted q.p.model q.p.t q.p.ht]
  simpa using NodeSemantics.model_count_bound q.p.model q.p.t q.p.ht H high
    (sourceHashes q) q.marked q.markedClause m hm

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end OAI.Algorithms
