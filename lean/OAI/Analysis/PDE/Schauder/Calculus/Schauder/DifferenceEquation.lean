import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DifferenceCalculus
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MatrixFunctional

/-! The exact variable-coefficient equation obeyed by a difference quotient. -/

noncomputable section
open Set
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Weak

theorem bilinear_difference_identity {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    (L : A →L[ℝ] B →L[ℝ] C) (I a₀ a₁ : A) (b₀ b₁ : B) (t : ℝ) :
    L (I - a₀) (t • (b₁ - b₀)) =
      t • (L (I - a₁) b₁ - L (I - a₀) b₀) + L (t • (a₁ - a₀)) b₁ := by
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_sub]
  abel

theorem nondivergence_differenceQuotient {m : ℕ}
    (B : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u f : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (v : EuclideanSpace ℝ (Fin m)) (h : ℝ) (x : EuclideanSpace ℝ (Fin m))
    (hx : nondivergenceOperator (fun y => 1 - B y) u x = f x)
    (hx' : nondivergenceOperator (fun y => 1 - B y) u (x + h • v) = f (x + h • v)) :
    nondivergenceOperator (fun y => 1 - B y) (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x =
      OAI.Analysis.PDE.Weak.differenceQuotient v h f x +
        matrixHessianFunctional (OAI.Analysis.PDE.Weak.differenceQuotient v h B x)
          (fderiv ℝ (fderiv ℝ u) (x + h • v)) := by
  change matrixHessianFunctional (1 - B x) (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Weak.differenceQuotient v h u)) x) = _
  rw [second_fderiv_differenceQuotient u hu v h x]
  have hid := bilinear_difference_identity (matrixHessianFunctionalCLM m) 1 (B x) (B (x + h • v))
    (fderiv ℝ (fderiv ℝ u) x) (fderiv ℝ (fderiv ℝ u) (x + h • v)) (h⁻¹)
  change matrixHessianFunctional (1 - B x) (OAI.Analysis.PDE.Weak.differenceQuotient v h (fderiv ℝ (fderiv ℝ u)) x) =
    h⁻¹ • (nondivergenceOperator (fun y => 1 - B y) u (x + h • v) -
      nondivergenceOperator (fun y => 1 - B y) u x) +
      matrixHessianFunctional (OAI.Analysis.PDE.Weak.differenceQuotient v h B x) (fderiv ℝ (fderiv ℝ u) (x + h • v)) at hid
  rw [hx, hx'] at hid
  exact hid

end OAI.Analysis.PDE.Schauder
