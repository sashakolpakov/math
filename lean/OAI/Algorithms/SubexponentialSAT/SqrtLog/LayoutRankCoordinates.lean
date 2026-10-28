import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank

namespace OAI.Algorithms

/-! Row and column enumeration preserves the rational rank of integer constraints. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open LayoutPullback LayoutExactBuckets

variable {J V W : Type*} [Fintype J] [Fintype V] [Fintype W]
variable [DecidableEq V] [DecidableEq W]

omit [Fintype W] [DecidableEq V] in
theorem row_equiv (e : V ≃ W) (a : V → ℤ) (w : W) :
    row e a w = a (e.symm w) := by
  simpa using row_apply_injective (fun v => e v) e.injective a (e.symm w)

omit [Fintype J] in
theorem rowRank_column_equiv (C : J → V → ℤ) (e : V ≃ W) :
    rowRank (fun j w => C j (e.symm w)) = rowRank C := by
  have hf : pulledConstraints (fun v => e v) C = (fun j w => C j (e.symm w)) := by
    funext j w
    exact row_equiv e (C j) w
  have hr : pulledConstraints (fun w => e.symm w) (fun j w => C j (e.symm w)) = C := by
    funext j v
    change row e.symm (fun w => C j (e.symm w)) v = C j v
    rw [row_equiv]
    simp
  apply le_antisymm
  · rw [← hf]
    exact rowRank_pullback_le (fun v => e v) C
  · have h := rowRank_pullback_le (fun w => e.symm w) (fun j w => C j (e.symm w))
    rw [hr] at h
    exact h

theorem rowRank_enumerated (C : J → V → ℤ) :
    rowRank (fun (j : Fin (Fintype.card J)) (v : Fin (Fintype.card V)) =>
      C ((Fintype.equivFin J).symm j) ((Fintype.equivFin V).symm v)) = rowRank C := by
  rw [rowRank_column_equiv (fun j => C ((Fintype.equivFin J).symm j)) (Fintype.equivFin V)]
  exact rowRank_reindex C _ (Fintype.equivFin J).symm.surjective

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
