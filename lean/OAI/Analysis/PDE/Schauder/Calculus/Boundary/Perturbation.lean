import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MatrixFunctional
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.SupportBounds

/-! The coefficient error on a halfspace is controlled by the genuine Hessian. -/

noncomputable section
open Set Laplacian
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

theorem matrix_hessian_contraction_sub_le {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) ℝ) (H K : EuclideanHessian m) :
    |matrixHessianFunctional A H - matrixHessianFunctional B K| ≤
      (m : ℝ) * m * (‖A‖ * ‖H - K‖ + ‖A - B‖ * ‖K‖) := by
  have he : matrixHessianFunctional A H - matrixHessianFunctional B K =
      matrixHessianFunctional A (H - K) + matrixHessianFunctional (A - B) K := by
    change (matrixHessianFunctionalCLM m A) H - (matrixHessianFunctionalCLM m B) K =
      (matrixHessianFunctionalCLM m A) (H - K) + (matrixHessianFunctionalCLM m (A - B)) K
    simp only [map_sub, sub_apply]
    ring
  have h₁ : |matrixHessianFunctional A (H - K)| ≤ (m : ℝ) * m * ‖A‖ * ‖H - K‖ := by
    exact ((matrixHessianFunctional A).le_opNorm (H - K)).trans
      (mul_le_mul_of_nonneg_right (norm_matrixHessianFunctional_le A) (norm_nonneg _))
  have h₂ : |matrixHessianFunctional (A - B) K| ≤ (m : ℝ) * m * ‖A - B‖ * ‖K‖ := by
    exact ((matrixHessianFunctional (A - B)).le_opNorm K).trans
      (mul_le_mul_of_nonneg_right (norm_matrixHessianFunctional_le _) (norm_nonneg _))
  rw [he]
  calc
    _ ≤ |matrixHessianFunctional A (H - K)| + |matrixHessianFunctional (A - B) K| := abs_add_le _ _
    _ ≤ (m : ℝ) * m * ‖A‖ * ‖H - K‖ + (m : ℝ) * m * ‖A - B‖ * ‖K‖ := add_le_add h₁ h₂
    _ = _ := by ring

theorem laplacian_perturbation_holder_on {m : ℕ}
    (B : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (s : Set (EuclideanSpace ℝ (Fin m)))
    {α θ M H K F : ℝ} (hθ : 0 ≤ θ) (hM : 0 ≤ M) (_ : 0 ≤ H) (_ : 0 ≤ K)
    (hclose : ∀ x ∈ s, ‖B x‖ ≤ θ)
    (hB : ∀ x ∈ s, ∀ y ∈ s, ‖B x - B y‖ ≤ M * ‖x - y‖ ^ α)
    (hDu : ∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ K)
    (hHu : ∀ x ∈ s, ∀ y ∈ s,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α)
    (hLu : ∀ x ∈ s, ∀ y ∈ s,
      |nondivergenceOperator (fun z => 1 - B z) u x - nondivergenceOperator (fun z => 1 - B z) u y| ≤
        F * ‖x - y‖ ^ α) :
    ∀ x ∈ s, ∀ y ∈ s, |laplacian u x - laplacian u y| ≤
      (F + (m : ℝ) * m * (θ * H + M * K)) * ‖x - y‖ ^ α := by
  have he (x) : laplacian u x - nondivergenceOperator (fun z => 1 - B z) u x =
      matrixHessianFunctional (B x) (fderiv ℝ (fderiv ℝ u) x) := by
    rw [laplacian_sub_nondivergenceOperator, matrixHessianFunctional_apply]
    congr 1
    ext i
    congr 1
    ext j
    simp only [Matrix.sub_apply, Matrix.one_apply]
    ring
  intro x hx y hy
  have hb := matrix_hessian_contraction_sub_le (B x) (B y)
    (fderiv ℝ (fderiv ℝ u) x) (fderiv ℝ (fderiv ℝ u) y)
  have hprod₁ := mul_le_mul (hclose x hx) (hHu x hx y hy) (norm_nonneg _) hθ
  have hprod₂ := mul_le_mul (hB x hx y hy) (hDu y hy) (norm_nonneg _)
    (mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _))
  have herr : |(laplacian u x - nondivergenceOperator (fun z => 1 - B z) u x) -
      (laplacian u y - nondivergenceOperator (fun z => 1 - B z) u y)| ≤
      (m : ℝ) * m * (θ * H + M * K) * ‖x - y‖ ^ α := by
    rw [he, he]
    apply hb.trans
    calc
      _ ≤ (m : ℝ) * m * (θ * (H * ‖x - y‖ ^ α) + (M * ‖x - y‖ ^ α) * K) :=
        mul_le_mul_of_nonneg_left (add_le_add hprod₁ hprod₂) (by positivity)
      _ = _ := by ring
  have hid : laplacian u x - laplacian u y =
      (nondivergenceOperator (fun z => 1 - B z) u x - nondivergenceOperator (fun z => 1 - B z) u y) +
      ((laplacian u x - nondivergenceOperator (fun z => 1 - B z) u x) -
        (laplacian u y - nondivergenceOperator (fun z => 1 - B z) u y)) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add (hLu x hx y hy) herr).trans_eq (by ring))

end OAI.Analysis.PDE.Schauder
