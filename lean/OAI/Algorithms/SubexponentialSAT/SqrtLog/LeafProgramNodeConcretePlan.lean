import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteLocality

namespace OAI.Algorithms

/-! The original-address source lookup is exactly the owner pullback used by
integer-bucket locality, including repeated owner incidences. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutSourceRowsProgram PerturbationAssembly LayoutPullback

variable {r Q d n : ℕ}

def planIndex (ps : List (ℕ × ℕ)) (n f j : ℕ) (h : (j,n+f)∈ps) : Fin ps.length :=
  ⟨ps.idxOf (j,n+f),by
    simpa only [List.idxOf,beq_eq_decide] using List.idxOf_lt_length_iff.mpr h⟩

theorem planIndex_get (ps : List (ℕ × ℕ)) (n f j : ℕ) (h : (j,n+f)∈ps) :
    ps.get (planIndex ps n f j h)=(j,n+f) := by
  simpa only [planIndex,List.idxOf,beq_eq_decide] using
    List.idxOf_get (List.idxOf_lt_length_iff.mpr h)

theorem fixedSourceRow_eq_pullback (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (f j : ℕ) (hj : (j,n+f)∈ps) (v : Fin n) :
    fixedSourceRow p ps P n f j v =
      row owner (packedValue P p.rows (planIndex ps n f j hj)) v := by
  let i := planIndex ps n f j hj
  unfold fixedSourceRow
  rw [sourceRowFamily_present _ _ _ _ _ _ hj]
  have hs := ownerSum_pullback (fun a : Fin ps.length => ps.get a) v.val
    (totalPackedSource p P i.val)
  rw [List.ofFn_get] at hs
  have hi : i.val=ps.idxOf (j,n+f) := by
    simp only [i,planIndex,List.idxOf,beq_eq_decide]
  rw [← hi,hs]
  unfold row
  apply Finset.sum_congr rfl
  intro a _
  simp only [howner,totalPackedSource,packedSourceValue,dite_eq_left i.isLt,dite_eq_left a.isLt,
    Fin.ext_iff]
  rfl

theorem fixedSourceRow_baseline_eq (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (f j : ℕ) (hj : (j,n+f)∈ps) (t : Fin Q) (x y : Fin n → ℤ)
    (hown : ∀ v,head t v=(P.label (planIndex ps n f j hj)).slot 0 t → x v=y v)
    (hother : ∀ g,g≠(P.label (planIndex ps n f j hj)).slot 0 t →
      LayoutExactBuckets.signature (fun (k : Fin ps.length) (v : {v : Fin n //head t v=g}) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t k.val v.val.val)
        (fun v=>x v.val) =
      LayoutExactBuckets.signature (fun (k : Fin ps.length) (v : {v : Fin n //head t v=g}) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t k.val v.val.val)
        (fun v=>y v.val)) :
    (∑ v,(fixedSourceRow p ps P n f j v).eval (p.model.node p.t Q p.ht p.hfield t)*
      (x v : p.model.O p.t)) =
    ∑ v,(fixedSourceRow p ps P n f j v).eval (p.model.node p.t Q p.ht p.hfield t)*
      (y v : p.model.O p.t) := by
  simp_rw [fixedSourceRow_eq_pullback p ps P owner howner f j hj]
  exact pulled_baseline_eq p P owner head hhead t (planIndex ps n f j hj) x y hown hother

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
