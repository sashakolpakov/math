import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteRows
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingIncidence

namespace OAI.Algorithms

/-! The physical factor jet evaluates to the common shifted source path as
soon as integer bucket locality identifies its merged-assignment baseline. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open DensePolynomialProgram LayoutProgram PerturbationAssembly
open Polynomial

variable {r Q d n : ℕ}

def storedPath (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (s : Fin 768 → List Bool) (x : Fin n → p.model.O p.t) (f j : ℕ) : Polynomial (p.model.O p.t) :=
  if (s 702).getD j false then C (if (s 703).getD j false then 1 else 0)
  else ∑ v, fixedSourceRow p ps P n f j v * C (x v)

theorem factorJet_eval (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (x : Fin n → p.model.O p.t) (hx : ∀ v,x v*x v=x v) (f j : ℕ)
    (hbase : (s 702).getD j false=false →
      (∑ v,(fixedSourceRow p ps P n f j v).eval (p.ops.decode theta)*
        (if (s 145).getD v.val false then 1 else 0)) =
      ∑ v,(fixedSourceRow p ps P n f j v).eval (p.ops.decode theta)*x v) :
    Moments.jetEval x hx (Factor.factorJet p ps P n f j theta s) =
      C ((storedPath p ps P s x f j).comp (X+C (p.ops.decode theta))) := by
  unfold Factor.factorJet sourceIncidenceJet
  simp only [Factor.choiceStore,show (574:Fin 768)≠546 by decide,
    show (575:Fin 768)≠546 by decide,show (575:Fin 768)≠574 by decide,
    ite_false,ite_true]
  cases hh : (s 702).getD j false
  · simp only [Bool.false_eq_true,ite_false,storedPath,hh]
    have he := Moments.incidenceZ_eval_row x hx (fixedSourceRow p ps P n f j)
      (p.ops.decode theta) _ (hbase hh)
    simp only [Moments.incidenceJet,Moments.jetEval,Polynomial.coe_mapRingHom,Polynomial.map_C]
    rw [he]
    congr 1
    simp only [Polynomial.sum_comp,Polynomial.mul_comp,Polynomial.C_comp]
  · simp only [storedPath,hh,ite_true,Polynomial.C_comp]
    rw [← Moments.ringScalar_eq_atom,NodeSemantics.jetEval_ringScalar]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
