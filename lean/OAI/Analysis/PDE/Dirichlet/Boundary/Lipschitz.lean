import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Coverage
import OAI.Analysis.PDE.Elliptic.Boundary.SlopeFromGradient

open Set Metric
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Elliptic

/-- A uniform derivative bound on a regular closed sublevel gives a local
Lipschitz bound there. This uses the convex flattened half-ball and never
assumes that the physical sublevel is convex. -/
theorem lipschitz_near_regular_sublevel {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : E → ℝ} (hr : ContDiff ℝ 3 r) (x : E)
    (hrx : r x = 0) (hreg : fderiv ℝ r x ≠ 0) {M : ℝ} (hM : 0 ≤ M) :
    ∃ ρ L : ℝ, 0 < ρ ∧ 0 < L ∧ ∀ f : E → F, ContDiff ℝ 1 f →
      (∀ z, r z ≤ 0 → ‖fderiv ℝ f z‖ ≤ M) →
      ∀ y ∈ closedBall x ρ, r y ≤ 0 → ∀ z ∈ closedBall x ρ, r z ≤ 0 →
        ‖f y - f z‖ ≤ L * ‖y - z‖ := by
  obtain ⟨v, c, C, G, P, hv, hc, hC, hG, hP, hG0, hchart⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_bounded_normalized_chart hr x hreg isOpen_univ (mem_univ x)
  obtain ⟨ρ, Cp, hρ, hCp, hcover, hLip⟩ := OAI.Analysis.PDE.Elliptic.exists_chart_coverage hP hG hG0
    (hchart 0 (by simp)).2.1
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlarge (q : E) (hq : q ∈ OAI.Analysis.PDE.Elliptic.closedHalfBall v) : q ∈ closedBall (0 : E) 2 := by
    simp only [mem_closedBall, dist_zero_right]
    linarith [hq.1]
  have hlevel (q : E) (hq : q ∈ OAI.Analysis.PDE.Elliptic.closedHalfBall v) : r (G q) ≤ 0 := by
    have hh := (hchart q (hlarge q hq)).2.2.1
    rw [hrx, sub_zero] at hh
    rw [hh]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hq.2
  have hcoord (y : E) (hy : y ∈ closedBall x ρ) (hry : r y ≤ 0) : P y ∈ OAI.Analysis.PDE.Elliptic.closedHalfBall v := by
    have hpy := (hcover y hy).2
    have hpy2 : P y ∈ closedBall (0 : E) 2 := by
      simp only [mem_closedBall, dist_zero_right]
      linarith
    have hh := (hchart (P y) hpy2).2.2.1
    rw [(hcover y hy).1, hrx, sub_zero] at hh
    exact ⟨by linarith, by nlinarith⟩
  refine ⟨ρ, (M + 1) * C * Cp, hρ, by positivity, ?_⟩
  intro f hf hDf y hy hry z hz hrz
  have hdiff (q : E) (_ : q ∈ OAI.Analysis.PDE.Elliptic.closedHalfBall v) : DifferentiableAt ℝ (f ∘ G) q :=
    (hf.differentiable (by norm_num) (G q)).comp q (hG.differentiable (by norm_num) q)
  have hbound (q : E) (hq : q ∈ OAI.Analysis.PDE.Elliptic.closedHalfBall v) : ‖fderiv ℝ (f ∘ G) q‖ ≤ M * C := by
    rw [fderiv_comp q (hf.differentiable (by norm_num) (G q)) (hG.differentiable (by norm_num) q)]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hDf (G q) (hlevel q hq)) (hchart q (hlarge q hq)).2.2.2.1
        (norm_nonneg _) hM)
  have hraw := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (OAI.Analysis.PDE.Elliptic.convex_closedHalfBall v)
    (hcoord z hz hrz) (hcoord y hy hry)
  change ‖f (G (P y)) - f (G (P z))‖ ≤ M * C * ‖P y - P z‖ at hraw
  rw [(hcover y hy).1, (hcover z hz).1] at hraw
  calc
    ‖f y - f z‖ ≤ M * C * ‖P y - P z‖ := hraw
    _ ≤ M * C * (Cp * ‖y - z‖) := mul_le_mul_of_nonneg_left (hLip y hy z hz) (mul_nonneg hM hC0)
    _ ≤ (M + 1) * C * Cp * ‖y - z‖ := by nlinarith [mul_nonneg (mul_nonneg hC0 hCp.le) (norm_nonneg (y - z))]

end OAI.Analysis.PDE.Dirichlet
