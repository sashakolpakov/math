import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Perturbation
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Absorption
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.LowerHolder

/-! From the flat Poisson estimate to a genuinely uniform small-coefficient estimate. -/

noncomputable section
open Set Metric Laplacian
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

local instance smallBoundaryFirstGroup (m : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance smallBoundaryFirstSpace (m : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance smallBoundarySecondGroup (m : ℕ) : NormedAddCommGroup (EuclideanHessian m) := inferInstance
local instance smallBoundarySecondSpace (m : ℕ) : NormedSpace ℝ (EuclideanHessian m) := inferInstance

theorem halfspace_small_coefficients {m : ℕ} (k : Fin m)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 3 u)
    (B : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    {R α C θ M F : ℝ} (hR : 0 ≤ R) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hs : tsupport u ⊆ closedBall 0 R)
    (hclose : ∀ x, 0 ≤ x k → ‖B x‖ ≤ θ)
    (hB : ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k → ‖B x - B y‖ ≤ M * ‖x - y‖ ^ α)
    (hLu : ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
      |nondivergenceOperator (fun z => 1 - B z) u x - nondivergenceOperator (fun z => 1 - B z) u y| ≤
        F * ‖x - y‖ ^ α)
    (hPoisson : ∀ K, 0 ≤ K →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k → |laplacian u x - laplacian u y| ≤ K * ‖x - y‖ ^ α) →
      ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * K * ‖x - y‖ ^ α)
    (hsmall : C * (m : ℝ) * m * (θ + M * (2 * R + 1) ^ α) ≤ 1 / 2) :
    ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ 2 * C * F * ‖x - y‖ ^ α := by
  have huc : HasCompactSupport u := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) R).of_isClosed_subset
    (isClosed_tsupport u) hs
  have hHc : HasCompactSupport (fderiv ℝ (fderiv ℝ u)) := (huc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)
  have hHC1 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  obtain ⟨H₀, hH₀, _, hinit⟩ := compact_C1_holder _ hHC1 hHc hα hα1
  have hfinal := geometric_holder_absorption (fderiv ℝ (fderiv ℝ u)) {x | 0 ≤ x k}
    α (C * F) H₀ (mul_nonneg hC hF) hH₀.le (fun x _ y _ => hinit x y)
  have hstep : ∀ H, 0 ≤ H →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) →
      ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ (C * F + H / 2) * ‖x - y‖ ^ α := by
    intro H hH hh
    have hsup := halfspace_hessian_bound_of_support k u hR hα hH hs hh
    have hforce := laplacian_perturbation_holder_on B u {x | 0 ≤ x k}
      hθ hM hH (mul_nonneg hH (Real.rpow_nonneg (by linarith) _))
      hclose hB hsup hh hLu
    have hest := hPoisson (F + (m : ℝ) * m * (θ * H + M * (H * (2 * R + 1) ^ α)))
      (by positivity) hforce
    intro x hx y hy
    apply (hest x hx y hy).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
    have hsmallH := mul_le_mul_of_nonneg_right hsmall hH
    nlinarith only [hsmallH]
  intro x hx y hy
  simpa only [mul_assoc] using hfinal hstep x hx y hy

end OAI.Analysis.PDE.Schauder
