import OAI.Analysis.PDE.Schauder.Calculus.Schauder.AffineHolder

/-! Quantitative entrywise bounds for the matrix coordinate changes. -/

noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

local instance boundaryMatrixGroup (m : ℕ) : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance boundaryMatrixSpace (m : ℕ) : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))
local instance boundaryMatrixOperatorGroup (m : ℕ) : NormedAddCommGroup
    (Matrix (Fin m) (Fin m) ℝ →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup ((Fin m → Fin m → ℝ) →L[ℝ] (Fin m → Fin m → ℝ)))

theorem elementwise_norm_mul_le {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) :
    ‖A * B‖ ≤ (m : ℝ) * ‖A‖ * ‖B‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k : Fin m, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin m, ‖A‖ * ‖B‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
        (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem elementwise_norm_transpose_le {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    ‖A.transpose‖ ≤ ‖A‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg A)).mpr
  intro i j
  exact Matrix.norm_entry_le_entrywise_sup_norm A

theorem norm_matrixCongruenceCLM_le {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) :
    ‖matrixCongruenceCLM P‖ ≤ (m : ℝ) ^ 2 * ‖P‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro A
  change ‖P * A * P.transpose‖ ≤ (m : ℝ) ^ 2 * ‖P‖ ^ 2 * ‖A‖
  calc
    _ ≤ (m : ℝ) * ‖P * A‖ * ‖P.transpose‖ := elementwise_norm_mul_le _ _
    _ ≤ (m : ℝ) * ((m : ℝ) * ‖P‖ * ‖A‖) * ‖P‖ := by
      gcongr
      · exact elementwise_norm_mul_le P A
      · exact elementwise_norm_transpose_le P
    _ = _ := by ring

theorem norm_matrix_of_euclideanCLM_le {m : ℕ}
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    ‖(Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).symm L‖ ≤ ‖L‖ := by
  let P := (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).symm L
  have hP : Matrix.toEuclideanCLM (𝕜 := ℝ) P = L :=
    (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).apply_symm_apply _
  apply (Matrix.norm_le_iff (norm_nonneg L)).mpr
  intro i j
  have he : P i j = L (EuclideanSpace.single j 1) i := by
    rw [← hP]
    exact (toEuclideanCLM_single P i j).symm
  change ‖P i j‖ ≤ ‖L‖
  rw [he]
  have hi := abs_real_inner_le_norm (EuclideanSpace.single i (1 : ℝ)) (L (EuclideanSpace.single j 1))
  have hj := L.le_opNorm (EuclideanSpace.single j 1)
  simp only [EuclideanSpace.inner_single_left, one_mul, PiLp.norm_single, norm_one,
    map_one, one_mul, mul_one] at hi hj
  have hcoord : ‖L (EuclideanSpace.single j 1) i‖ ≤ ‖L (EuclideanSpace.single j 1)‖ := by
    simpa only [Real.norm_eq_abs] using hi
  exact hcoord.trans hj

end OAI.Analysis.PDE.Schauder
