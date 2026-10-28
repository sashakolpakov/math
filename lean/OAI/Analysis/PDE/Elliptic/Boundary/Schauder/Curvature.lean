import OAI.Analysis.PDE.Elliptic.Boundary.Curvature

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance schauderCurvatureSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance schauderCurvatureSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance schauderCurvatureHessianGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance schauderCurvatureHessianSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The lower-order Hessian chart error is linear in the solution's
lower-jet bound; the chart constants are kept separate. -/
theorem chartCurvature_lipschitz_linear
    {u : E → ℝ} {G : E → E} {S : Set E} {L N : ℝ}
    (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 3 G) (hS : Convex ℝ S)
    (hL : 0 ≤ L) (hN : 0 ≤ N)
    (hu1 : ∀ z ∈ S, ‖fderiv ℝ u (G z)‖ ≤ N)
    (hu2 : ∀ z ∈ S, ‖fderiv ℝ (gradient u) (G z)‖ ≤ N)
    (hG1 : ∀ z ∈ S, ‖fderiv ℝ G z‖ ≤ L)
    (hG2 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 G z‖ ≤ L)
    (hG3 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 3 G z‖ ≤ L)
    {z z' : E} (hz : z ∈ S) (hz' : z' ∈ S) :
    ‖chartCurvature u G z - chartCurvature u G z'‖ ≤ (L^2 + L) * N * ‖z-z'‖ := by
  have hDG : ContDiff ℝ 2 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hD2G : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ G)) := hDG.fderiv_right (by norm_num)
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hda (y) : DifferentiableAt ℝ (fun y => fderiv ℝ u (G y)) y :=
    (hDu.differentiable (by norm_num) (G y)).comp y (hG.differentiable (by norm_num) y)
  have hba (y) (hy : y ∈ S) : ‖fderiv ℝ (fun y => fderiv ℝ u (G y)) y‖ ≤ N*L := by
    rw [show fderiv ℝ (fun y => fderiv ℝ u (G y)) y =
        (fderiv ℝ (fderiv ℝ u) (G y)).comp (fderiv ℝ G y) from
        ((hDu.differentiable (by norm_num) (G y)).hasFDerivAt.comp y
          (hG.differentiable (by norm_num) y).hasFDerivAt).fderiv]
    have hh := (fderiv ℝ (fderiv ℝ u) (G y)).opNorm_comp_le (fderiv ℝ G y)
    rw [← norm_fderiv_gradient hu] at hh
    exact hh.trans (mul_le_mul (hu2 y hy) (hG1 y hy) (norm_nonneg _) hN)
  have ha := Convex.norm_image_sub_le_of_norm_fderiv_le (fun y (_ : y ∈ S) => hda y) hba hS hz' hz
  have hb := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y (_ : y ∈ S) => hD2G.differentiable (by norm_num) y)
    (fun y hy => (third_fderiv_norm_le_iterated y).trans (hG3 y hy)) hS hz' hz
  apply (chartCurvature_difference (hG.of_le (by norm_num)) u z z').trans
  have h1 := mul_le_mul ha ((second_fderiv_norm_le_iterated z).trans (hG2 z hz))
    (norm_nonneg _) (show 0 ≤ N*L*‖z-z'‖ by positivity)
  have h2 := mul_le_mul (hu1 z' hz') hb (norm_nonneg _) hN
  nlinarith

theorem chartCurvature_norm_linear
    {u : E → ℝ} {G : E → E} {z : E} {L N : ℝ}
    (hG : ContDiffAt ℝ 2 G z) (hN : 0 ≤ N)
    (hu1 : ‖fderiv ℝ u (G z)‖ ≤ N) (hG2 : ‖iteratedFDeriv ℝ 2 G z‖ ≤ L) :
    ‖chartCurvature u G z‖ ≤ L*N := by
  exact (hessian_linear_comp_norm _ hG).trans
    ((mul_le_mul hu1 hG2 (norm_nonneg _) hN).trans_eq (mul_comm _ _))

end OAI.Analysis.PDE.Elliptic
