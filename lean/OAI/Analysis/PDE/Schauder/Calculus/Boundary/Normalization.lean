import OAI.Analysis.PDE.Schauder.Boundary.SchauderNormalization
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.MatrixBounds

/-! Boundary-preserving elliptic normalization in matrix coordinates. -/

noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

theorem normalization_matrices_of_equiv {m : ℕ}
    (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (A : Matrix (Fin m) (Fin m) ℝ) (hL : linearEllipticMatrix L.toContinuousLinearMap = A) :
    ∃ P Q : Matrix (Fin m) (Fin m) ℝ,
      Matrix.toEuclideanCLM (𝕜 := ℝ) P = L.toContinuousLinearMap ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) Q = L.symm.toContinuousLinearMap ∧
      P * Q = 1 ∧ Q * P = 1 ∧ Q * A * Q.transpose = 1 ∧
      ‖P‖ ≤ ‖L.toContinuousLinearMap‖ ∧ ‖Q‖ ≤ ‖L.symm.toContinuousLinearMap‖ := by
  let P := (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).symm L.toContinuousLinearMap
  let Q := (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).symm L.symm.toContinuousLinearMap
  have hP : Matrix.toEuclideanCLM (𝕜 := ℝ) P = L.toContinuousLinearMap :=
    (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).apply_symm_apply _
  have hQ : Matrix.toEuclideanCLM (𝕜 := ℝ) Q = L.symm.toContinuousLinearMap :=
    (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).apply_symm_apply _
  have hPQ : P * Q = 1 := by
    apply (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).injective
    rw [map_mul, map_one]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) P * Matrix.toEuclideanCLM (𝕜 := ℝ) Q = 1
    rw [hP, hQ]
    apply ContinuousLinearMap.ext
    intro x
    exact L.apply_symm_apply x
  have hQP : Q * P = 1 := by
    apply (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).injective
    rw [map_mul, map_one]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) Q * Matrix.toEuclideanCLM (𝕜 := ℝ) P = 1
    rw [hP, hQ]
    apply ContinuousLinearMap.ext
    intro x
    exact L.symm_apply_apply x
  have hAeq : A = P * P.transpose := by
    rw [← hL, ← hP, linearEllipticMatrix_toEuclideanCLM]
  refine ⟨P, Q, hP, hQ, hPQ, hQP, ?_, norm_matrix_of_euclideanCLM_le _, norm_matrix_of_euclideanCLM_le _⟩
  rw [hAeq]
  calc
    _ = (Q * P) * (Q * P).transpose := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hQP, Matrix.transpose_one, mul_one]

theorem exists_boundary_normalization_matrices {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef) (k : Fin m)
    {ell Λ : ℝ} (hell : 0 < ell) (hΛ : 0 ≤ Λ)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin m), ell * ‖x‖ ^ 2 ≤
      inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) A x))
    (hupper : ∀ x : EuclideanSpace ℝ (Fin m),
      inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) A x) ≤ Λ * ‖x‖ ^ 2) :
    ∃ (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
      (P Q : Matrix (Fin m) (Fin m) ℝ) (c : ℝ),
      0 < c ∧ (∀ x, L x k = c * x k) ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) P = L.toContinuousLinearMap ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) Q = L.symm.toContinuousLinearMap ∧
      P * Q = 1 ∧ Q * P = 1 ∧ Q * A * Q.transpose = 1 ∧
      ‖L.toContinuousLinearMap‖ ≤ Real.sqrt Λ ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹ ∧
      ‖Q‖ ≤ (Real.sqrt ell)⁻¹ := by
  obtain ⟨L, c, hc, hL, hnormal, hnorm, hinv⟩ :=
    exists_boundary_elliptic_normalization_bounded A hA k hell hΛ hlower hupper
  obtain ⟨P, Q, hP, hQ, hPQ, hQP, hQA, _, hQnorm⟩ := normalization_matrices_of_equiv L A hL
  exact ⟨L, P, Q, c, hc, hnormal, hP, hQ, hPQ, hQP, hQA, hnorm, hinv, hQnorm.trans hinv⟩

end OAI.Analysis.PDE.Schauder
