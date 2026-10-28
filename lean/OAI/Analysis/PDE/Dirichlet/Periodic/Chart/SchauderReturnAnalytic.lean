import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationCurvature

open Set InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance returnFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance returnFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance returnSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance returnSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance returnChartSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance returnChartSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- Curvature variation uses convexity separately in physical and chart
coordinates, not convexity of the physical domain being estimated. -/
theorem chartCurvature_lipschitz_between_sets
    {w : E → ℝ} {P : E → E} {D S : Set E} {L M : ℝ}
    (hw : ContDiff ℝ 2 w) (hP : ContDiff ℝ 3 P)
    (hD : Convex ℝ D) (hS : Convex ℝ S) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hw1 : ∀ z ∈ S, ‖fderiv ℝ w z‖ ≤ M)
    (hw2 : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ w) z‖ ≤ M)
    (hP1 : ∀ z ∈ D, ‖fderiv ℝ P z‖ ≤ L)
    (hP2 : ∀ z ∈ D, ‖iteratedFDeriv ℝ 2 P z‖ ≤ L)
    (hP3 : ∀ z ∈ D, ‖iteratedFDeriv ℝ 3 P z‖ ≤ L)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) (hPx : P x ∈ S) (hPy : P y ∈ S) :
    ‖OAI.Analysis.PDE.Elliptic.chartCurvature w P x-OAI.Analysis.PDE.Elliptic.chartCurvature w P y‖ ≤ (L^2+L)*M*‖x-y‖ := by
  have hPxPy : ‖P x-P y‖ ≤ L*‖x-y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hP.differentiable (by norm_num) z) hP1 hD hy hx
  have ha0 : ‖fderiv ℝ w (P x)-fderiv ℝ w (P y)‖ ≤ M*‖P x-P y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ (hw.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z)
      hw2 hS hPy hPx
  have ha : ‖fderiv ℝ w (P x)-fderiv ℝ w (P y)‖ ≤ M*L*‖x-y‖ :=
    ha0.trans ((mul_le_mul_of_nonneg_left hPxPy hM).trans_eq (by ring))
  have hD2P : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ P)) :=
    (hP.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  have hb : ‖fderiv ℝ (fderiv ℝ P) x-fderiv ℝ (fderiv ℝ P) y‖ ≤ L*‖x-y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hD2P.differentiable (by norm_num) z)
      (fun z hz ↦ (OAI.Analysis.PDE.Elliptic.third_fderiv_norm_le_iterated z).trans (hP3 z hz)) hD hy hx
  apply (OAI.Analysis.PDE.Elliptic.chartCurvature_difference (hP.of_le (by norm_num)) w x y).trans
  have h1 := mul_le_mul ha ((OAI.Analysis.PDE.Elliptic.second_fderiv_norm_le_iterated x).trans (hP2 x hx))
    (norm_nonneg _) (show 0 ≤ M*L*‖x-y‖ by positivity)
  have h2 := mul_le_mul (hw1 (P y) hPy) hb (norm_nonneg _) hM
  nlinarith

/-- Hessian chain-rule bounds on an arbitrary subset of a compact chart
region. Solution derivatives are used only on the convex chart image set. -/
theorem chart_hessian_holder_between_sets
    {w : E → ℝ} {P : E → E} {D S T : Set E} {L M d α : ℝ}
    (hw : ContDiff ℝ 2 w) (hP : ContDiff ℝ 3 P)
    (hD : Convex ℝ D) (hS : Convex ℝ S) (hTD : T ⊆ D) (hPS : MapsTo P T S)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hscale : ∀ x ∈ D, ∀ y ∈ D, ‖x-y‖ ≤ d*‖x-y‖^α)
    (hw1 : ∀ z ∈ S, ‖fderiv ℝ w z‖ ≤ M)
    (hw2 : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ w) z‖ ≤ M)
    (hwα : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (fderiv ℝ w) x-fderiv ℝ (fderiv ℝ w) y‖ ≤ M*‖x-y‖^α)
    (hP1 : ∀ z ∈ D, ‖fderiv ℝ P z‖ ≤ L)
    (hP2 : ∀ z ∈ D, ‖iteratedFDeriv ℝ 2 P z‖ ≤ L)
    (hP3 : ∀ z ∈ D, ‖iteratedFDeriv ℝ 3 P z‖ ≤ L) :
    (∀ x ∈ T, ‖fderiv ℝ (fderiv ℝ (fun z ↦ w (P z))) x‖ ≤ (L^2+L)*M) ∧
    (∀ x ∈ T, ∀ y ∈ T,
      ‖fderiv ℝ (fderiv ℝ (fun z ↦ w (P z))) x-
        fderiv ℝ (fderiv ℝ (fun z ↦ w (P z))) y‖ ≤
          (L^2*L^α+(3*L^2+L)*d)*M*‖x-y‖^α) := by
  let J := fun x ↦ (fderiv ℝ P x).adjoint
  let A := fderiv ℝ (gradient w)
  let B := fun x ↦ OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator (J x) (A (P x))
  have hwc : ContDiff ℝ 2 (fun z ↦ w (P z)) := hw.comp (hP.of_le (by norm_num))
  have hAn x (hx : x ∈ S) : ‖A x‖ ≤ M := by
    dsimp [A]
    rw [OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient hw]
    exact hw2 x hx
  have hAh x (hx : x ∈ S) y (hy : y ∈ S) : ‖A x-A y‖ ≤ M*‖x-y‖^α := by
    dsimp [A]
    rw [OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient_sub hw]
    exact hwα x hx y hy
  have hJn x (hx : x ∈ D) : ‖J x‖ ≤ L := by
    simpa only [J,ContinuousLinearMap.adjoint.norm_map] using hP1 x hx
  have hJh x (hx : x ∈ D) y (hy : y ∈ D) : ‖J x-J y‖ ≤ L*‖x-y‖ := by
    change ‖(fderiv ℝ P x).adjoint-(fderiv ℝ P y).adjoint‖ ≤ _
    rw [← map_sub,ContinuousLinearMap.adjoint.norm_map]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ (hP.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num) z)
      (fun z hz ↦ (OAI.Analysis.PDE.Elliptic.second_fderiv_norm_le_iterated z).trans (hP2 z hz)) hD hy hx
  have hPh x (hx : x ∈ D) y (hy : y ∈ D) : ‖P x-P y‖ ≤ L*‖x-y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hP.differentiable (by norm_num) z) hP1 hD hy hx
  have hBn x (hx : x ∈ T) : ‖B x‖ ≤ L^2*M := by
    apply (OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator_norm_bound _ _).trans
    exact mul_le_mul (by nlinarith [norm_nonneg (J x),hJn x (hTD hx)])
      (hAn (P x) (hPS hx)) (norm_nonneg _) (sq_nonneg L)
  have hBh x (hx : x ∈ T) y (hy : y ∈ T) :
      ‖B x-B y‖ ≤ (L^2*L^α+2*L^2*d)*M*‖x-y‖^α := by
    have hJxy : ‖J x-J y‖ ≤ L*d*‖x-y‖^α :=
      (hJh x (hTD hx) y (hTD hy)).trans
        ((mul_le_mul_of_nonneg_left (hscale x (hTD hx) y (hTD hy)) hL).trans_eq (by ring))
    have hAxy : ‖A (P x)-A (P y)‖ ≤ M*L^α*‖x-y‖^α := by
      calc
        _ ≤ M*‖P x-P y‖^α := hAh (P x) (hPS hx) (P y) (hPS hy)
        _ ≤ M*(L*‖x-y‖)^α := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hPh x (hTD hx) y (hTD hy)) hα) hM
        _ = _ := by rw [Real.mul_rpow hL (norm_nonneg _)]; ring
    calc
      _ ≤ ‖J x‖^2*‖A (P x)-A (P y)‖ + ‖J x-J y‖*‖A (P y)‖*‖J x‖ +
          ‖J y‖*‖A (P y)‖*‖J x-J y‖ := OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator_variation _ _ _ _
      _ ≤ L^2*(M*L^α*‖x-y‖^α) + (L*d*‖x-y‖^α)*M*L + L*M*(L*d*‖x-y‖^α) := by
        gcongr
        all_goals first | exact hJn x (hTD hx) | exact hJn y (hTD hy) |
          exact hAn (P y) (hPS hy)
      _ = _ := by ring
  have he x : fderiv ℝ (gradient (fun z ↦ w (P z))) x = B x+OAI.Analysis.PDE.Elliptic.chartCurvature w P x := by
    simpa only [B,J,A,OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator,ContinuousLinearMap.adjoint_adjoint,
      OAI.Analysis.PDE.Elliptic.chartCurvature] using OAI.Analysis.PDE.Elliptic.hessianOperator_comp hw.contDiffAt (hP.of_le (by norm_num)).contDiffAt
  constructor
  · intro x hx
    rw [← OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient hwc,he]
    have hc := OAI.Analysis.PDE.Elliptic.chartCurvature_norm_linear (hP.of_le (by norm_num)).contDiffAt hM
      (hw1 (P x) (hPS hx)) (hP2 x (hTD hx))
    exact (norm_add_le _ _).trans ((add_le_add (hBn x hx) hc).trans_eq (by ring))
  · intro x hx y hy
    rw [← OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient_sub hwc,he x,he y]
    have hid : (B x+OAI.Analysis.PDE.Elliptic.chartCurvature w P x)-(B y+OAI.Analysis.PDE.Elliptic.chartCurvature w P y) =
        (B x-B y)+(OAI.Analysis.PDE.Elliptic.chartCurvature w P x-OAI.Analysis.PDE.Elliptic.chartCurvature w P y) := by abel
    rw [hid]
    have hc := chartCurvature_lipschitz_between_sets hw hP hD hS hL hM hw1 hw2
      hP1 hP2 hP3 (hTD hx) (hTD hy) (hPS hx) (hPS hy)
    have hc' := hc.trans (mul_le_mul_of_nonneg_left (hscale x (hTD hx) y (hTD hy))
      (show 0 ≤ (L^2+L)*M by positivity))
    exact (norm_add_le _ _).trans ((add_le_add (hBh x hx y hy) hc').trans_eq (by ring))

end OAI.Analysis.PDE.Dirichlet
