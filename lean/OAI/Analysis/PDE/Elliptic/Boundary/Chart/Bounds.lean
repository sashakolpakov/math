import OAI.Analysis.PDE.Elliptic.Boundary.Flattening

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem eventually_C3_derivative_bounds {f : E → F} {x : E} (hf : ContDiffAt ℝ 3 f x) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x,
      ContDiffAt ℝ 3 f y ∧ ‖fderiv ℝ f y‖ ≤ C ∧
      ‖iteratedFDeriv ℝ 2 f y‖ ≤ C ∧
      ‖iteratedFDeriv ℝ 3 f y‖ ≤ C := by
  have h1 : ContDiffAt ℝ 2 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  have h2 : ContinuousAt (iteratedFDeriv ℝ 2 f) x := hf.continuousAt_iteratedFDeriv (by norm_num)
  have h3 : ContinuousAt (iteratedFDeriv ℝ 3 f) x := hf.continuousAt_iteratedFDeriv (by norm_num)
  let C := ‖fderiv ℝ f x‖ + ‖iteratedFDeriv ℝ 2 f x‖ + ‖iteratedFDeriv ℝ 3 f x‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have h1C : ‖fderiv ℝ f x‖ < C := by
    dsimp [C]; linarith [norm_nonneg (iteratedFDeriv ℝ 2 f x), norm_nonneg (iteratedFDeriv ℝ 3 f x)]
  have h2C : ‖iteratedFDeriv ℝ 2 f x‖ < C := by
    dsimp [C]; linarith [norm_nonneg (fderiv ℝ f x), norm_nonneg (iteratedFDeriv ℝ 3 f x)]
  have h3C : ‖iteratedFDeriv ℝ 3 f x‖ < C := by
    dsimp [C]; linarith [norm_nonneg (fderiv ℝ f x), norm_nonneg (iteratedFDeriv ℝ 2 f x)]
  refine ⟨C, hC, ?_⟩
  filter_upwards [hf.eventually (by norm_num),
    h1.continuousAt.norm.tendsto.eventually (eventually_lt_nhds h1C),
    h2.norm.tendsto.eventually (eventually_lt_nhds h2C),
    h3.norm.tendsto.eventually (eventually_lt_nhds h3C)] with y hy h1y h2y h3y
  exact ⟨hy, h1y.le, h2y.le, h3y.le⟩

theorem eventually_derivative_close_id {f : E → E} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (hD : fderiv ℝ f x = ContinuousLinearMap.id ℝ E) :
    ∀ᶠ y in 𝓝 x, ‖fderiv ℝ f y - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 := by
  have hc : ContinuousAt (fun y => ‖fderiv ℝ f y - ContinuousLinearMap.id ℝ E‖) x :=
    ((hf.fderiv_right (m := 2) (by norm_num)).continuousAt.sub continuousAt_const).norm
  have hh : ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ < 1 / 2 := by rw [hD]; norm_num
  exact (hc.tendsto.eventually (eventually_lt_nhds hh)).mono (fun _ h => h.le)

/-- The chart and its inverse have bounded first three derivatives on a
smaller closed neighborhood, and both Jacobians remain near the identity.
All constants arise from the defining function, before any PDE solution. -/
theorem exists_bounded_boundary_flattening [CompleteSpace E]
    {r : E → ℝ} (hr : ContDiff ℝ 3 r) (x : E) (hg : fderiv ℝ r x ≠ 0) :
    ∃ (w : E) (F : E → E) (R C : ℝ), 0 < R ∧ 0 < C ∧ fderiv ℝ r x w = 1 ∧ F 0 = x ∧
      HasFDerivAt F (ContinuousLinearMap.id ℝ E) 0 ∧
      ∀ y ∈ Metric.closedBall 0 R,
        ContDiffAt ℝ 3 F y ∧
        flatteningMap r x (fderiv ℝ r x) w (F y) = y ∧
        r (F y) - r x = fderiv ℝ r x y ∧
        ‖fderiv ℝ F y - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 ∧
        ‖fderiv ℝ (flatteningMap r x (fderiv ℝ r x) w) (F y) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 ∧
        ‖fderiv ℝ F y‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F y‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 3 F y‖ ≤ C ∧
        ‖fderiv ℝ (flatteningMap r x (fderiv ℝ r x) w) (F y)‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 2 (flatteningMap r x (fderiv ℝ r x) w) (F y)‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 3 (flatteningMap r x (fderiv ℝ r x) w) (F y)‖ ≤ C := by
  obtain ⟨w, F, R, hR, hw, hF0, hDF, hF, hinv, hlevel⟩ := exists_boundary_flattening hr x hg
  have h00 : (0 : E) ∈ Metric.closedBall 0 R := by simp [hR.le]
  have hFbase := hF 0 h00
  let P := flatteningMap r x (fderiv ℝ r x) w
  have hP : ContDiffAt ℝ 3 P x := (contDiff_flatteningMap hr x _ w).contDiffAt
  have hDP : fderiv ℝ P x = ContinuousLinearMap.id ℝ E :=
    (hasFDerivAt_flatteningMap (hr.differentiable (by norm_num) x).hasFDerivAt w).fderiv
  obtain ⟨C1, hC1, hbF⟩ := eventually_C3_derivative_bounds hFbase
  obtain ⟨C2, hC2, hbP⟩ := eventually_C3_derivative_bounds hP
  have hlim : Tendsto F (𝓝 0) (𝓝 x) := by simpa only [hF0] using hFbase.continuousAt.tendsto
  have hgood : ∀ᶠ y in 𝓝 (0 : E), y ∈ Metric.closedBall 0 R ∧
      (ContDiffAt ℝ 3 F y ∧ ‖fderiv ℝ F y‖ ≤ C1 ∧ ‖iteratedFDeriv ℝ 2 F y‖ ≤ C1 ∧
        ‖iteratedFDeriv ℝ 3 F y‖ ≤ C1) ∧
      (ContDiffAt ℝ 3 P (F y) ∧ ‖fderiv ℝ P (F y)‖ ≤ C2 ∧ ‖iteratedFDeriv ℝ 2 P (F y)‖ ≤ C2 ∧
        ‖iteratedFDeriv ℝ 3 P (F y)‖ ≤ C2) ∧
      ‖fderiv ℝ F y - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 ∧
      ‖fderiv ℝ P (F y) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : E) hR, hbF, hlim.eventually hbP,
      eventually_derivative_close_id hFbase hDF.fderiv,
      hlim.eventually (eventually_derivative_close_id hP hDP)] with y hy hyF hyP hcloseF hcloseP
    exact ⟨hy, hyF, hyP, hcloseF, hcloseP⟩
  obtain ⟨ε, hε, heps⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨w, F, ε / 2, max C1 C2, by positivity, lt_max_of_lt_left hC1,
    hw, hF0, hDF, ?_⟩
  intro y hy
  have hs := heps (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε) hy)
  exact ⟨hs.2.1.1, hinv y hs.1, hlevel y hs.1, hs.2.2.2.1, hs.2.2.2.2,
    hs.2.1.2.1.trans (le_max_left _ _), hs.2.1.2.2.1.trans (le_max_left _ _),
    hs.2.1.2.2.2.trans (le_max_left _ _), hs.2.2.1.2.1.trans (le_max_right _ _),
    hs.2.2.1.2.2.1.trans (le_max_right _ _), hs.2.2.1.2.2.2.trans (le_max_right _ _)⟩

end OAI.Analysis.PDE.Elliptic
