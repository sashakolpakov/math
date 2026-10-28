import OAI.Analysis.PDE.Elliptic.Boundary.Schauder.Coefficient
import OAI.Analysis.PDE.Elliptic.Boundary.Schauder.Curvature

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Quantitative C²,α composition with a fixed C³ chart, retaining both
the original exponent and linear dependence on the solution norm. -/
theorem chart_hessian_holder_linear
    {u : E → ℝ} {G : E → E} {S : Set E} {L N α : ℝ}
    (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 3 G) (hS : Convex ℝ S)
    (hL : 0 ≤ L) (hN : 0 ≤ N) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    (hu1 : ∀ z ∈ S, ‖fderiv ℝ u (G z)‖ ≤ N)
    (hu2 : ∀ z ∈ S, ‖fderiv ℝ (gradient u) (G z)‖ ≤ N)
    (huα : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (gradient u) (G x)-fderiv ℝ (gradient u) (G y)‖ ≤ N*‖G x-G y‖^α)
    (hG1 : ∀ z ∈ S, ‖fderiv ℝ G z‖ ≤ L)
    (hG2 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 G z‖ ≤ L)
    (hG3 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 3 G z‖ ≤ L) :
    (∀ x ∈ S, ‖fderiv ℝ (gradient (fun y => u (G y))) x‖ ≤ (L^2+L)*N) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (gradient (fun y => u (G y))) x -
        fderiv ℝ (gradient (fun y => u (G y))) y‖ ≤
          (L^2*L^α + 3*L^2+L)*N*‖x-y‖^α) := by
  let J := fun x => (fderiv ℝ G x).adjoint
  let A := fderiv ℝ (gradient u)
  have hJn : ∀ x ∈ S, ‖J x‖ ≤ L := by
    intro x hx
    simpa only [J, ContinuousLinearMap.adjoint.norm_map] using hG1 x hx
  have hJh : ∀ x ∈ S, ∀ y ∈ S, ‖J x-J y‖ ≤ L*‖x-y‖ := by
    intro x hx y hy
    change ‖(fderiv ℝ G x).adjoint-(fderiv ℝ G y).adjoint‖ ≤ _
    rw [← map_sub, ContinuousLinearMap.adjoint.norm_map]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hG.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num) z)
      (fun z hz => (second_fderiv_norm_le_iterated z).trans (hG2 z hz)) hS hy hx
  have hGh : ∀ x ∈ S, ∀ y ∈ S, ‖G x-G y‖ ≤ L*‖x-y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hG.differentiable (by norm_num) z) hG1 hS hy hx
  obtain ⟨hn, hh⟩ := pullback_coefficient_holder_on_unit_diameter A G J hL hN hα hα1
    hdiam hu2 huα hJn hJh hGh
  let B := fun x => pullbackEllipticOperator (J x) (A (G x))
  have he (x : E) : fderiv ℝ (gradient (fun y => u (G y))) x = B x + chartCurvature u G x := by
    simpa only [B, J, A, pullbackEllipticOperator, ContinuousLinearMap.adjoint_adjoint,
      chartCurvature] using hessianOperator_comp hu.contDiffAt (hG.of_le (by norm_num)).contDiffAt
  constructor
  · intro x hx
    rw [he]
    have hc := chartCurvature_norm_linear (hG.of_le (by norm_num)).contDiffAt hN (hu1 x hx) (hG2 x hx)
    exact (norm_add_le _ _).trans ((add_le_add (hn x hx) hc).trans_eq (by ring))
  · intro x hx y hy
    rw [he x, he y]
    have hid : (B x + chartCurvature u G x) - (B y + chartCurvature u G y) =
        (B x-B y) + (chartCurvature u G x-chartCurvature u G y) := by abel
    rw [hid]
    have hc := chartCurvature_lipschitz_linear hu hG hS hL hN hu1 hu2 hG1 hG2 hG3 hx hy
    have hd : ‖x-y‖ ≤ ‖x-y‖^α := Real.self_le_rpow_of_le_one (norm_nonneg _) (hdiam x hx y hy) hα1
    have hc' := hc.trans (mul_le_mul_of_nonneg_left hd (show 0 ≤ (L^2+L)*N by positivity))
    exact (norm_add_le _ _).trans ((add_le_add (hh x hx y hy) hc').trans_eq (by ring))

end OAI.Analysis.PDE.Elliptic
