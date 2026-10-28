import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteBaseline

namespace OAI.Algorithms

/-! The native factor source jet and the fixed global target share the same
shifted path on every literal incidence actually queried by the factor. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open DensePolynomialProgram SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open LayoutProgram PerturbationAssembly Polynomial

variable {r Q d n : ℕ}

theorem factorJet_eval_branch (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (high : H → Bool)
    (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (x : ResidualEmbedding.Free H → Bool) (f : ℕ) (j : Fin n)
    (hpresent : (j.val,n+f)∈ps)
    (hmask : (s 702).getD j.val false = decide (j∈H))
    (hhigh : ∀ hj:j∈H,(s 703).getD j.val false=high ⟨j,hj⟩)
    (hzero : ∀ v∈H,fixedSourceRow p ps P n f j.val v=0)
    (hbase : j∉H → baseline (n:=n) p ps P theta s f j.val =
      ∑ v : ResidualEmbedding.Free H,
        (fixedSourceRow p ps P n f j.val v.val).eval (p.ops.decode theta)*HashInput.boolValue (x v)) :
    Moments.jetEval (Squarefree.boolValue (HighIncidence.glue H high x))
      (Squarefree.boolValue_idempotent (HighIncidence.glue H high x))
      (Factor.factorJet p ps P n f j.val theta s) =
    C ((NodeSemantics.branchPath H high (completedRows p ps P H) x f j).comp
      (X + C (p.ops.decode theta))) := by
  rw [factorJet_embedding p ps P H high theta s f j hmask hhigh hzero,
    ResidualEmbedding.eval_jet_branch]
  exact residualJet_eval p ps P H high theta s x f j hpresent hbase

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
