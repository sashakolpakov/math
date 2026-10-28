import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteRows
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsCountSource

namespace OAI.Algorithms

/-! A total source target with the original variable IDs. Missing incidences
are filled by identity rows only in this mathematical totalization; scoped
factor evaluation never reads those rows. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram PerturbationAssembly

variable {r Q d n : ℕ}

def completedRows (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (f : ℕ) (j : Fin n) (v : ResidualEmbedding.Free H) :
    Polynomial (p.model.O p.t) :=
  if (j.val,n+f) ∈ ps then fixedSourceRow p ps P n f j.val v.val
  else Polynomial.C (if v.val=j then 1 else 0)

theorem completedRows_present (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (f : ℕ) (j : Fin n) (v : ResidualEmbedding.Free H)
    (hj : (j.val,n+f)∈ps) :
    completedRows p ps P H f j v = fixedSourceRow p ps P n f j.val v.val := by
  simp only [completedRows,ite_eq_left hj]

theorem completedRows_origin (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (f : ℕ) (j v : ResidualEmbedding.Free H) :
    (completedRows p ps P H f j.val v).eval 0 = if v=j then 1 else 0 := by
  by_cases hj : (j.val.val,n+f)∈ps
  · simp only [completedRows,ite_eq_left hj]
    rw [fixedSourceRow_origin p ps P n f j.val.val v.val hj]
    simp only [Subtype.ext_iff,Fin.ext_iff]
  · simp only [completedRows,ite_eq_right hj,Polynomial.eval_C,Subtype.ext_iff]

theorem completedRows_degree (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (f : ℕ) (j : Fin n) (v : ResidualEmbedding.Free H) :
    (completedRows p ps P H f j v).natDegree ≤ p.R := by
  by_cases hj : (j.val,n+f)∈ps
  · simpa only [completedRows,ite_eq_left hj] using fixedSourceRow_degree p ps P n f j.val v.val
  · simp only [completedRows,ite_eq_right hj,Polynomial.natDegree_C,Nat.zero_le]

theorem completed_target_count {C : Type*} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (ops : SubexponentialSAT.SubexpSymbolicCost.RepresentedRing C (ZMod (3^p.t)))
    (half : C) (hhalf : 2*ops.decode half=1)
    (H : Finset (Fin n)) (high : H → Bool)
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) :
    (NodeSemantics.target H p.t (NodeSemantics.computedDigits ops (p.model.base p.t) p.t half)
      (NodeSemantics.liftedHashes p.model p.t hashes) marked clause
      (NodeSemantics.branchPath H high (completedRows p ps P H))).eval 0 =
      (NodeSemantics.ternaryFixedHighCount H high hashes marked clause : p.model.O p.t) :=
  NodeSemantics.model_target_ternary_count p.model p.t p.ht ops half hhalf H high
    (completedRows p ps P H) (completedRows_origin p ps P H) hashes marked clause

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
