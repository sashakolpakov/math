import OAI.Analysis.PDE.Elliptic.Boundary.Schauder.Hessian

open Set InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The chart estimate on any bounded convex set. `D` records only the
fixed conversion from Lipschitz differences to exponent `α`. -/
theorem chart_hessian_holder_bounded
    {u : E → ℝ} {G : E → E} {S : Set E} {L N D α : ℝ}
    (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 3 G) (hS : Convex ℝ S)
    (hL : 0 ≤ L) (hN : 0 ≤ N) (hD : 0 ≤ D) (hα : 0 ≤ α)
    (hscale : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ D*‖x-y‖^α)
    (hu1 : ∀ z ∈ S, ‖fderiv ℝ u (G z)‖ ≤ N)
    (hu2 : ∀ z ∈ S, ‖fderiv ℝ (gradient u) (G z)‖ ≤ N)
    (huα : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (gradient u) (G x)-fderiv ℝ (gradient u) (G y)‖ ≤ N*‖G x-G y‖^α)
    (hG1 : ∀ z ∈ S, ‖fderiv ℝ G z‖ ≤ L)
    (hG2 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 G z‖ ≤ L)
    (hG3 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 3 G z‖ ≤ L) :
    (∀ x ∈ S, ‖fderiv ℝ (gradient (fun y ↦ u (G y))) x‖ ≤ (L^2+L)*N) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (gradient (fun z ↦ u (G z))) x-
        fderiv ℝ (gradient (fun z ↦ u (G z))) y‖ ≤
          (L^2*L^α+(3*L^2+L)*D)*N*‖x-y‖^α) := by
  let J := fun x ↦ (fderiv ℝ G x).adjoint
  let A := fderiv ℝ (gradient u)
  let B := fun x ↦ OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator (J x) (A (G x))
  have hJn x (hx : x ∈ S) : ‖J x‖ ≤ L := by
    simpa only [J,ContinuousLinearMap.adjoint.norm_map] using hG1 x hx
  have hJh x (hx : x ∈ S) y (hy : y ∈ S) : ‖J x-J y‖ ≤ L*‖x-y‖ := by
    change ‖(fderiv ℝ G x).adjoint-(fderiv ℝ G y).adjoint‖ ≤ _
    rw [← map_sub,ContinuousLinearMap.adjoint.norm_map]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ (hG.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num) z)
      (fun z hz ↦ (OAI.Analysis.PDE.Elliptic.second_fderiv_norm_le_iterated z).trans (hG2 z hz)) hS hy hx
  have hGh x (hx : x ∈ S) y (hy : y ∈ S) : ‖G x-G y‖ ≤ L*‖x-y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hG.differentiable (by norm_num) z) hG1 hS hy hx
  have hBn x (hx : x ∈ S) : ‖B x‖ ≤ L^2*N := by
    apply (OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator_norm_bound _ _).trans
    exact mul_le_mul (by nlinarith [norm_nonneg (J x),hJn x hx]) (hu2 x hx)
      (norm_nonneg _) (sq_nonneg L)
  have hBh x (hx : x ∈ S) y (hy : y ∈ S) :
      ‖B x-B y‖ ≤ (L^2*L^α+2*L^2*D)*N*‖x-y‖^α := by
    have hJxy : ‖J x-J y‖ ≤ L*D*‖x-y‖^α :=
      (hJh x hx y hy).trans ((mul_le_mul_of_nonneg_left (hscale x hx y hy) hL).trans_eq (by ring))
    have hAxy : ‖A (G x)-A (G y)‖ ≤ N*L^α*‖x-y‖^α := by
      calc
        _ ≤ N*‖G x-G y‖^α := huα x hx y hy
        _ ≤ N*(L*‖x-y‖)^α := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hGh x hx y hy) hα) hN
        _ = _ := by rw [Real.mul_rpow hL (norm_nonneg _)]; ring
    calc
      _ ≤ ‖J x‖^2*‖A (G x)-A (G y)‖ + ‖J x-J y‖*‖A (G y)‖*‖J x‖ +
          ‖J y‖*‖A (G y)‖*‖J x-J y‖ := OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator_variation _ _ _ _
      _ ≤ L^2*(N*L^α*‖x-y‖^α) + (L*D*‖x-y‖^α)*N*L +
          L*N*(L*D*‖x-y‖^α) := by
        gcongr
        all_goals first | exact hJn x hx | exact hJn y hy | exact hu2 y hy
      _ = _ := by ring
  have he x : fderiv ℝ (gradient (fun y ↦ u (G y))) x = B x+OAI.Analysis.PDE.Elliptic.chartCurvature u G x := by
    simpa only [B,J,A,OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator,ContinuousLinearMap.adjoint_adjoint,
      OAI.Analysis.PDE.Elliptic.chartCurvature] using OAI.Analysis.PDE.Elliptic.hessianOperator_comp hu.contDiffAt (hG.of_le (by norm_num)).contDiffAt
  constructor
  · intro x hx
    rw [he]
    have hc := OAI.Analysis.PDE.Elliptic.chartCurvature_norm_linear (hG.of_le (by norm_num)).contDiffAt hN (hu1 x hx) (hG2 x hx)
    exact (norm_add_le _ _).trans ((add_le_add (hBn x hx) hc).trans_eq (by ring))
  · intro x hx y hy
    rw [he x,he y]
    have hid : (B x+OAI.Analysis.PDE.Elliptic.chartCurvature u G x)-(B y+OAI.Analysis.PDE.Elliptic.chartCurvature u G y) =
        (B x-B y)+(OAI.Analysis.PDE.Elliptic.chartCurvature u G x-OAI.Analysis.PDE.Elliptic.chartCurvature u G y) := by abel
    rw [hid]
    have hc := OAI.Analysis.PDE.Elliptic.chartCurvature_lipschitz_linear hu hG hS hL hN hu1 hu2 hG1 hG2 hG3 hx hy
    have hc' := hc.trans (mul_le_mul_of_nonneg_left (hscale x hx y hy)
      (show 0 ≤ (L^2+L)*N by positivity))
    exact (norm_add_le _ _).trans ((add_le_add (hBh x hx y hy) hc').trans_eq (by ring))

end OAI.Analysis.PDE.Dirichlet
