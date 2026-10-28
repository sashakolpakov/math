import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramProducedRankMatrix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgramInterface

namespace OAI.Algorithms

/-! Literal equality between the runtime owner-fiber sum and an integer
matrix column. Both use the original incidence order and original owner IDs. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open scoped BigOperators

/-- The executable fiber scanner selects exactly the matching indices.
No nodup or arbitrary re-enumeration premise is needed. -/
theorem fiber_sum_ofFn {D : ℕ} (ps : Fin D → ℕ × ℕ) (value : ℕ → ℤ)
    (query start : ℕ) :
    ((LayoutOwnerFiberProgram.fiberIndices query start (List.ofFn ps)).map value).sum=
      ∑ i : Fin D,if (ps i).1=query then value (start+i.val) else 0 := by
  induction D generalizing start with
  | zero => simp [LayoutOwnerFiberProgram.fiberIndices]
  | succ D ih =>
      rw [List.ofFn_succ,LayoutOwnerFiberProgram.fiberIndices,Fin.sum_univ_succ]
      by_cases h : (ps 0).1=query
      · simp only [h,ite_true,List.map_cons,List.sum_cons]
        rw [ih]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        simp [Nat.add_left_comm,Nat.add_comm]
      · simp only [h,ite_false,zero_add]
        rw [ih]
        apply Finset.sum_congr rfl
        intro i _
        simp [Nat.add_left_comm,Nat.add_comm]

/-- A physical owner-fiber result computes this exact literal matrix, even
when incidence factors and variable labels are not consecutive. -/
def fiberMatrix {D n : ℕ} (owner : Fin D → Fin n)
    (entry : Fin D → Fin D → ℤ) : Fin D → Fin n → ℤ :=
  fun j v=>∑ i,if owner i=v then entry j i else 0

theorem fiber_sum_eq_matrix {D n : ℕ} (owner : Fin D → Fin n)
    (ps : Fin D → ℕ × ℕ) (hp : ∀ i,(ps i).1=(owner i).val)
    (entry : Fin D → Fin D → ℤ) (value : ℕ → ℕ → ℤ)
    (hv : ∀ j i,value j.val i.val=entry j i) (j : Fin D) (v : Fin n) :
    ((LayoutOwnerFiberProgram.fiberIndices v.val 0 (List.ofFn ps)).map (value j.val)).sum=
      fiberMatrix owner entry j v := by
  rw [fiber_sum_ofFn]
  unfold fiberMatrix
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.zero_add,hp,hv]
  have he : (owner i).val=v.val ↔ owner i=v := Fin.ext_iff.symm
  simp only [he]

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end OAI.Algorithms
