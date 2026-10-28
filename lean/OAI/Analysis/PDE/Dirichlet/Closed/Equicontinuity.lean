import OAI.Analysis.PDE.Dirichlet.Boundary.Lipschitz
import OAI.Analysis.PDE.Dirichlet.JetCompactness

open Set Metric
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

theorem lipschitz_near_closed_sublevel {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (x : E) (hx : r x ≤ 0) {M : ℝ} (hM : 0 ≤ M) :
    ∃ ρ L : ℝ, 0 < ρ ∧ 0 < L ∧ ∀ f : E → F, ContDiff ℝ 1 f →
      (∀ z, r z ≤ 0 → ‖fderiv ℝ f z‖ ≤ M) →
      ∀ y ∈ closedBall x ρ, r y ≤ 0 → ∀ z ∈ closedBall x ρ, r z ≤ 0 →
        ‖f y - f z‖ ≤ L * ‖y - z‖ := by
  by_cases hzero : r x = 0
  · exact lipschitz_near_regular_sublevel hr x hzero (hreg x hzero) hM
  have hneg : r x < 0 := lt_of_le_of_ne hx hzero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt hr.continuous continuous_const).mem_nhds hneg)
  have hclosed : ∀ y ∈ closedBall x (ε / 2), r y ≤ 0 := by
    intro y hy
    exact (hball (closedBall_subset_ball (by linarith : ε / 2 < ε) hy)).le
  refine ⟨ε / 2, M + 1, by positivity, by positivity, ?_⟩
  intro f hf hDf y hy _ z hz _
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun q (_ : q ∈ closedBall x (ε / 2)) ↦ hf.differentiable (by norm_num) q)
    (fun q hq ↦ hDf q (hclosed q hq)) (convex_closedBall x (ε / 2)) hz hy
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- Actual first derivative bounds give equicontinuity right up to a
regular physical boundary, without a global convexity assumption. -/
theorem equicontinuous_regular_sublevel {E F J : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (f : J → E → F) (hf : ∀ j, ContDiff ℝ 1 (f j)) {M : ℝ} (hM : 0 ≤ M)
    (hDf : ∀ j z, r z ≤ 0 → ‖fderiv ℝ (f j) z‖ ≤ M) :
    Equicontinuous (fun j (x : {x | r x ≤ 0}) ↦ f j x) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨ρ, L, hρ, hL, hb⟩ := lipschitz_near_closed_sublevel (F := F) hr hreg x x.property hM
  refine ⟨min ρ (ε / L), lt_min hρ (div_pos hε hL), ?_⟩
  intro y hy j
  have hyρ : y.val ∈ closedBall x.val ρ := by
    have hh := hy.trans_le (min_le_left ρ (ε / L))
    simpa only [mem_closedBall, Subtype.dist_eq, dist_comm] using hh.le
  have hh := hb (f j) (hf j) (hDf j) x (by simpa using hρ.le) x.property y hyρ y.property
  have hnear : dist x.val y.val < ε / L := by
    simpa only [Subtype.dist_eq, dist_comm] using hy.trans_le (min_le_right ρ (ε / L))
  have hsmall : L * dist x.val y.val < ε := by
    have h := (lt_div_iff₀ hL).mp hnear
    simpa only [mul_comm] using h
  exact (show dist (f j x) (f j y) ≤ L * dist x.val y.val by
    simpa only [dist_eq_norm] using hh).trans_lt hsmall

end OAI.Analysis.PDE.Dirichlet
