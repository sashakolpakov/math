import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Pointwise

/-! Constant real matrix congruences of the nondivergence operator. -/

noncomputable section
open Set Matrix
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

theorem sum_four_exchange {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ι → κ → κ → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem bilinear_matrix_congruence {m : ℕ}
    (H : EuclideanHessian m) (A P : Matrix (Fin m) (Fin m) ℝ) :
    (∑ i, ∑ j, A i j * H
      (Matrix.toEuclideanCLM (𝕜 := ℝ) P (EuclideanSpace.single i 1))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) P (EuclideanSpace.single j 1))) =
      ∑ k, ∑ l, (P * A * P.transpose) k l *
        H (EuclideanSpace.single k 1) (EuclideanSpace.single l 1) := by
  have he : (∑ i, ∑ j, A i j * H
      (Matrix.toEuclideanCLM (𝕜 := ℝ) P (EuclideanSpace.single i 1))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) P (EuclideanSpace.single j 1))) =
      ∑ i, ∑ j, ∑ k, ∑ l, A i j * (P k i * P l j *
        H (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [euclidean_bilinear_expansion H]
    simp only [toEuclideanCLM_single, Finset.mul_sum]
  rw [he, sum_four_exchange]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def matrixCongruenceCLM {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ →L[ℝ] Matrix (Fin m) (Fin m) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A => P * A * P.transpose
    map_add' := by intro A B; simp only [Matrix.mul_add, Matrix.add_mul]
    map_smul' := by intro c A; simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }

@[simp] theorem matrixCongruenceCLM_apply {m : ℕ} (P A : Matrix (Fin m) (Fin m) ℝ) :
    matrixCongruenceCLM P A = P * A * P.transpose := rfl

theorem nondivergence_comp_affine_matrix {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (P : Matrix (Fin m) (Fin m) ℝ) (x₀ x : EuclideanSpace ℝ (Fin m)) :
    nondivergenceOperator A (fun y => u (x₀ + Matrix.toEuclideanCLM (𝕜 := ℝ) P y)) x =
      ∑ k, ∑ l, (P * A x * P.transpose) k l *
        fderiv ℝ (fderiv ℝ u) (x₀ + Matrix.toEuclideanCLM (𝕜 := ℝ) P x)
          (EuclideanSpace.single k 1) (EuclideanSpace.single l 1) := by
  unfold nondivergenceOperator
  simp_rw [second_fderiv_comp_affine u hu]
  exact bilinear_matrix_congruence _ _ _

end OAI.Analysis.PDE.Schauder
