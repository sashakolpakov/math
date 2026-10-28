import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutPullback
import OAI.Algorithms.SubexponentialSAT.Truncation

namespace OAI.Algorithms

/-! The exact polynomial computed by the native owner-fiber traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
open scoped BigOperators

variable {A : Type*}

def ownerSum [AddMonoid A] (ps : List (ℕ × ℕ)) (owner : ℕ) (value : ℕ → A) : A :=
  ((LayoutOwnerFiberProgram.fiberIndices owner 0 ps).map value).sum

theorem fiber_sum_zipIdx [AddMonoid A] (ps : List (ℕ × ℕ)) (owner index : ℕ) (value : ℕ → A) :
    ((LayoutOwnerFiberProgram.fiberIndices owner index ps).map value).sum=
      ((ps.zipIdx index).map (fun x => if x.1.1=owner then value x.2 else 0)).sum := by
  induction ps generalizing index with
  | nil => rfl
  | cons p ps ih =>
      by_cases h : p.1=owner <;>
        simp [LayoutOwnerFiberProgram.fiberIndices,h,ih]

theorem ownerSum_zipIdx [AddMonoid A] (ps : List (ℕ × ℕ)) (owner : ℕ) (value : ℕ → A) :
    ownerSum ps owner value=
      ((ps.zipIdx).map (fun x => if x.1.1=owner then value x.2 else 0)).sum :=
  fiber_sum_zipIdx ps owner 0 value

theorem fiber_empty_of_no_owner (ps : List (ℕ × ℕ)) (owner index : ℕ)
    (h : ∀ p∈ps, p.1≠owner) :
    LayoutOwnerFiberProgram.fiberIndices owner index ps=[] := by
  induction ps generalizing index with
  | nil => rfl
  | cons p ps ih =>
      have hp := h p (by simp)
      have ht : ∀ q∈ps, q.1≠owner := by intro q hq; exact h q (by simp [hq])
      simp [LayoutOwnerFiberProgram.fiberIndices,hp,ih (index+1) ht]

theorem ownerSum_zero [AddMonoid A] (ps : List (ℕ × ℕ)) (owner : ℕ) (value : ℕ → A)
    (h : ∀ p∈ps, p.1≠owner) : ownerSum ps owner value=0 := by
  simp [ownerSum,fiber_empty_of_no_owner ps owner 0 h]

theorem ownerSum_pullback [AddCommMonoid A] {n : ℕ} (ps : Fin n → ℕ × ℕ)
    (owner : ℕ) (value : ℕ → A) :
    ownerSum (List.ofFn ps) owner value=
      LayoutPullback.row (fun i : Fin n => (ps i).1) (fun i => value i.val) owner := by
  have hzip : (List.ofFn ps).zipIdx=List.ofFn (fun i : Fin n => (ps i,i.val)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [ownerSum_zipIdx,hzip]
  simp [LayoutPullback.row,List.map_ofFn,List.sum_ofFn]

section Polynomial
variable [CommRing A]

theorem list_sum_degree (ps : List (Polynomial A)) (R : ℕ)
    (h : ∀ p∈ps, p.natDegree ≤ R) : ps.sum.natDegree ≤ R := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp := h p (by simp)
      have ht := ih (by intro q hq; exact h q (by simp [hq]))
      exact (Polynomial.natDegree_add_le p ps.sum).trans (max_le hp ht)

theorem ownerSum_degree (ps : List (ℕ × ℕ)) (owner : ℕ) (value : ℕ → Polynomial A) (R : ℕ)
    (h : ∀ i∈LayoutOwnerFiberProgram.fiberIndices owner 0 ps, (value i).natDegree ≤ R) :
    (ownerSum ps owner value).natDegree ≤ R := by
  apply list_sum_degree
  intro p hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  exact h i hi

theorem trunc_full_degree (P : Polynomial A) (R : ℕ) (h : P.natDegree ≤ R) :
    Truncation.trunc (R+1) P=P := by
  ext j
  rw [Truncation.coeff_trunc]
  split_ifs with hj
  · rfl
  · symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega

/-- The full T cutoff is independent of the later Z-jet cutoff. -/
theorem ownerSum_full_degree (ps : List (ℕ × ℕ)) (owner : ℕ) (value : ℕ → Polynomial A) (R : ℕ)
    (h : ∀ i∈LayoutOwnerFiberProgram.fiberIndices owner 0 ps, (value i).natDegree ≤ R) :
    Truncation.trunc (R+1) (ownerSum ps owner value)=ownerSum ps owner value :=
  trunc_full_degree _ R (ownerSum_degree ps owner value R h)

end Polynomial
end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
