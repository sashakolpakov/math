import OAI.LinearAlgebra.Moore.Rank.Mixed.Definition

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.Calculus.Quaternion
open scoped ComplexOrder

/-- A sum of selected rank-one matrices is a congruence of a diagonal
projection, including when the selected vectors are linearly dependent. -/
theorem sum_outer_eq_diagonal_congruence {m : ℕ}
    (v : Fin m → Fin m → Quaternion ℝ) (S : Finset (Fin m)) :
    (∑ i ∈ S, OAI.Analysis.Calculus.Quaternion.outer (v i)) =
      (of fun i j => v j i) *
        Matrix.diagonal (fun i => ((if i ∈ S then 1 else 0 : ℝ) : Quaternion ℝ)) *
        (of fun i j => v j i)ᴴ := by
  classical
  have hcast : (fun i : Fin m => ((if i ∈ S then 1 else 0 : ℝ) : Quaternion ℝ)) =
      (fun i => if i ∈ S then 1 else 0) := by
    funext i
    split_ifs <;> rfl
  rw [hcast]
  apply Matrix.ext
  intro i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.diagonal, Matrix.conjTranspose_apply]
  simp [OAI.Analysis.Calculus.Quaternion.outer, mul_ite, ite_mul]

/-- Fewer than `m` rank-one directions have zero Moore determinant. -/
theorem mooreDet_sum_outer_eq_zero_of_ne_univ {m : ℕ}
    (v : Fin m → Fin m → Quaternion ℝ) {S : Finset (Fin m)}
    (hS : S ≠ Finset.univ) : mooreDet m (∑ i ∈ S, OAI.Analysis.Calculus.Quaternion.outer (v i)) = 0 := by
  classical
  rw [sum_outer_eq_diagonal_congruence, mooreDet_congruence, mooreDet_real_diagonal]
  obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
    by_contra h
    push Not at h
    exact hS (Finset.eq_univ_of_forall h)
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]

theorem mooreDet_sum_outer_nonneg {m : ℕ}
    (v : Fin m → Fin m → Quaternion ℝ) :
    0 ≤ mooreDet m (∑ i, OAI.Analysis.Calculus.Quaternion.outer (v i)) := by
  apply mooreDet_nonneg_of_complexify_posSemidef
  classical
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, complexify_zero]; exact Matrix.PosSemidef.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, complexify_add]
    exact (complexify_outer_posSemidef (v a)).add ih

end OAI.LinearAlgebra.Moore
