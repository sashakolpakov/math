import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteJets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteTarget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingMoments

namespace OAI.Algorithms

/-! Source jets live in the free-coordinate squarefree algebra even though
the runtime stores every key at its original ambient ID. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open DensePolynomialProgram LayoutProgram PerturbationAssembly Polynomial

variable {r Q d n : ℕ}

def baseline (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool) (f j : ℕ) :=
  ∑ v : Fin n, (fixedSourceRow p ps P n f j v).eval (p.ops.decode theta)*
    (if (s 145).getD v.val false then 1 else 0)

def residualJet (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (high : H → Bool)
    (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (f : ℕ) (j : Fin n) : Squarefree.Jet (ResidualEmbedding.Free H) (p.model.O p.t) :=
  if hj : j∈H then Moments.ringScalar (HashInput.boolValue (high ⟨j,hj⟩))
  else Moments.incidenceJet (fun v : ResidualEmbedding.Free H => fixedSourceRow p ps P n f j.val v.val)
    (p.ops.decode theta) (baseline (n:=n) p ps P theta s f j.val)

theorem fixedSourceRow_pad (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (f j : ℕ)
    (hzero : ∀ v∈H, fixedSourceRow p ps P n f j v=0) :
    ResidualEmbedding.padZero H
      (fun v : ResidualEmbedding.Free H => fixedSourceRow p ps P n f j v.val) =
      fixedSourceRow p ps P n f j := by
  funext v
  by_cases hv : v∈H
  · rw [ResidualEmbedding.padZero_high H _ v hv,hzero v hv]
  · exact ResidualEmbedding.padZero_low H _ ⟨v,hv⟩

theorem factorJet_embedding (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (high : H → Bool)
    (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (f : ℕ) (j : Fin n)
    (hmask : (s 702).getD j.val false = decide (j∈H))
    (hhigh : ∀ hj:j∈H,(s 703).getD j.val false=high ⟨j,hj⟩)
    (hzero : ∀ v∈H,fixedSourceRow p ps P n f j.val v=0) :
    Factor.factorJet p ps P n f j.val theta s =
      ResidualEmbedding.jet (ResidualEmbedding.inclusion H)
        (residualJet p ps P H high theta s f j) := by
  unfold Factor.factorJet sourceIncidenceJet
  simp only [Factor.choiceStore,show (574:Fin 768)≠546 by decide,
    show (575:Fin 768)≠546 by decide,show (575:Fin 768)≠574 by decide,
    ite_false,ite_true,hmask]
  by_cases hj : j∈H
  · simp only [residualJet,dite_eq_left hj]
    simp only [hj,decide_true,ite_true,hhigh hj]
    rw [ResidualEmbedding.jet_ringScalar]
    exact (Moments.ringScalar_eq_atom _).symm
  · simp only [residualJet,dite_eq_right hj]
    simp only [hj,decide_false,Bool.false_eq_true,ite_false]
    rw [ResidualEmbedding.incidenceJet_pad,fixedSourceRow_pad p ps P H f j.val hzero]
    rfl


theorem residualJet_eval (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (high : H → Bool)
    (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (x : ResidualEmbedding.Free H → Bool) (f : ℕ) (j : Fin n)
    (hpresent : (j.val,n+f)∈ps)
    (hbase : j∉H → baseline (n:=n) p ps P theta s f j.val =
      ∑ v : ResidualEmbedding.Free H,
        (fixedSourceRow p ps P n f j.val v.val).eval (p.ops.decode theta)*HashInput.boolValue (x v)) :
    Moments.jetEval (Squarefree.boolValue x) (Squarefree.boolValue_idempotent x)
      (residualJet p ps P H high theta s f j) =
    C ((NodeSemantics.branchPath H high (completedRows p ps P H) x f j).comp
      (X + C (p.ops.decode theta))) := by
  by_cases hj : j∈H
  · simp only [residualJet,dite_eq_left hj,NodeSemantics.jetEval_ringScalar,
      NodeSemantics.branchPath,Polynomial.C_comp]
  · simp only [residualJet,dite_eq_right hj,NodeSemantics.branchPath]
    simp_rw [completedRows_present p ps P H f j _ hpresent]
    have he := Moments.incidenceZ_eval_row (Squarefree.boolValue x)
      (Squarefree.boolValue_idempotent x)
      (fun v : ResidualEmbedding.Free H => fixedSourceRow p ps P n f j.val v.val)
      (p.ops.decode theta) _ (hbase hj)
    simp only [Moments.incidenceJet,Moments.jetEval,Polynomial.coe_mapRingHom,Polynomial.map_C]
    rw [he]
    congr 1
    simp only [Polynomial.sum_comp,Polynomial.mul_comp,Polynomial.C_comp,Squarefree.boolValue,HashInput.boolValue]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
