import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteResidual
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcretePlan

namespace OAI.Algorithms

/-! Exact integer bucket signatures restore the baseline used in a native
factor jet to the value of the shared fixed-high source path. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open DensePolynomialProgram SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open LayoutProgram PerturbationAssembly

variable {r Q d n : ℕ}

def boolInt (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem boolInt_cast {R : Type*} [CommRing R] (b : Bool) :
    (boolInt b : R)=HashInput.boolValue b := by cases b <;> simp [boolInt,HashInput.boolValue]

theorem sum_free_rows (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (high : H → Bool) (a : ResidualEmbedding.Free H → Bool)
    (f j : ℕ) (theta : p.model.O p.t)
    (hzero : ∀ v∈H,fixedSourceRow p ps P n f j v=0) :
    (∑ v,(fixedSourceRow p ps P n f j v).eval theta *
      HashInput.boolValue (HighIncidence.glue H high a v)) =
    ∑ v : ResidualEmbedding.Free H,(fixedSourceRow p ps P n f j v.val).eval theta *
      HashInput.boolValue (a v) := by
  rw [← ResidualEmbedding.sum_padZero H]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v∈H
  · rw [hzero v hv,ResidualEmbedding.padZero_high H _ v hv]
    simp
  · simp only [ResidualEmbedding.padZero,not_false_eq_true,hv,dite_eq_left,HighIncidence.glue,dite_eq_right]

theorem baseline_eq_free (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (high : H → Bool) (a : ResidualEmbedding.Free H → Bool)
    (theta : Coeff (baseWidth 3 p.t) d) (s : Fin 768 → List Bool)
    (f j : ℕ) (hj : (j,n+f)∈ps) (t : Fin Q)
    (htheta : p.ops.decode theta=p.model.node p.t Q p.ht p.hfield t)
    (hzero : ∀ v∈H,fixedSourceRow p ps P n f j v=0)
    (hown : ∀ v,head t v=(P.label (planIndex ps n f j hj)).slot 0 t →
      (s 145).getD v.val false=HighIncidence.glue H high a v)
    (hother : ∀ g,g≠(P.label (planIndex ps n f j hj)).slot 0 t →
      LayoutExactBuckets.signature (fun (k : Fin ps.length) (v : {v : Fin n //head t v=g}) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t k.val v.val.val)
        (fun v=>boolInt ((s 145).getD v.val.val false)) =
      LayoutExactBuckets.signature (fun (k : Fin ps.length) (v : {v : Fin n //head t v=g}) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t k.val v.val.val)
        (fun v=>boolInt (HighIncidence.glue H high a v.val))) :
    baseline (n:=n) p ps P theta s f j =
      ∑ v : ResidualEmbedding.Free H,(fixedSourceRow p ps P n f j v.val).eval (p.ops.decode theta)*
        HashInput.boolValue (a v) := by
  have h := fixedSourceRow_baseline_eq p ps P owner howner head hhead f j hj t
    (fun v=>boolInt ((s 145).getD v.val false))
    (fun v=>boolInt (HighIncidence.glue H high a v))
    (fun v hv=>congrArg boolInt (hown v hv)) hother
  simp only [boolInt_cast,← htheta] at h
  change (∑ v,(fixedSourceRow p ps P n f j v).eval (p.ops.decode theta)*
    HashInput.boolValue ((s 145).getD v.val false)) = _
  exact h.trans (sum_free_rows p ps P H high a f j (p.ops.decode theta) hzero)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
