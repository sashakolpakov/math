import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ShiftGeometry
import OAI.Analysis.Calculus.SmoothExtension.Periodic.TangentPeriodization
import OAI.Analysis.PDE.Elliptic.PeriodicChartCoverage

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.SmoothExtension

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [AddCommGroup T]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem disjoint_period_translates_of_radius (L : T →+ E)
    {d R : ℝ} (hgap : ∀ z : T, z ≠ 0 → d ≤ ‖L z‖) (hR : 2 * R < d) (a : E) :
    ∀ x z w, x + L z ∈ closedBall a R → x + L w ∈ closedBall a R → z = w := by
  intro x z w hz hw
  by_contra hne
  have hzw : z - w ≠ 0 := sub_ne_zero.mpr hne
  have hl := hgap (z - w) hzw
  have ht := dist_triangle (x + L z) a (x + L w)
  have he : dist (x + L z) (x + L w) = ‖L (z-w)‖ := by
    simp only [dist_eq_norm, map_sub]
    congr 1
    abel
  rw [he, dist_comm a] at ht
  have hz' : dist (x + L z) a ≤ R := hz
  have hw' : dist (x + L w) a ≤ R := hw
  linarith

/-- Nested coordinate and physical cutoffs. The physical cutoff is identically
one on the image of the coordinate support, preventing spurious chart terms. -/
theorem exists_nested_chart_cutoffs {G : E → E} (hG : Continuous G)
    {a : E} (hG0 : G 0 = a) {R : ℝ} (hR : 0 < R) :
    ∃ ρ η : E → ℝ, ContDiff ℝ ∞ ρ ∧ ContDiff ℝ ∞ η ∧
      HasCompactSupport η ∧
      (∀ x, R ≤ dist x a → ρ x = 0) ∧
      Function.support η ⊆ ball 0 1 ∧
      (∀ z, η z ≠ 0 → ρ (G z) = 1) ∧
      (ρ =ᶠ[𝓝 a] fun _ ↦ 1) ∧ (η =ᶠ[𝓝 (0 : E)] fun _ ↦ 1) := by
  let ρ : ContDiffBump a := ⟨R/2, R, by positivity, by linarith⟩
  have hpre : G ⁻¹' ball a (R/2) ∈ 𝓝 (0 : E) :=
    hG.continuousAt.preimage_mem_nhds (by rw [hG0]; exact ball_mem_nhds a (by positivity))
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hpre
  let s : ℝ := min (ε/2) (1/2)
  have hs : 0 < s := lt_min (by positivity) (by norm_num)
  have hsε : s < ε := (min_le_left _ _).trans_lt (by linarith)
  have hs1 : s < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let η : ContDiffBump (0 : E) := ⟨s/2, s, by positivity, by linarith⟩
  refine ⟨ρ, η, ρ.contDiff, η.contDiff, η.hasCompactSupport, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ρ.zero_of_le_dist hx
  · intro z hz
    have hdist : dist z 0 < s := by
      by_contra hn
      exact hz (η.zero_of_le_dist (le_of_not_gt hn))
    exact hdist.trans hs1
  · intro z hz
    have hdist : dist z 0 < s := by
      by_contra hn
      exact hz (η.zero_of_le_dist (le_of_not_gt hn))
    have him : G z ∈ ball a (R/2) := hb (hdist.trans hsε)
    exact ρ.one_of_mem_closedBall (ball_subset_closedBall him)
  · filter_upwards [ball_mem_nhds a (show 0 < R/2 by positivity)] with x hx
    exact ρ.one_of_mem_closedBall (ball_subset_closedBall hx)
  · filter_upwards [ball_mem_nhds (0 : E) (show 0 < s/2 by positivity)] with x hx
    exact η.one_of_mem_closedBall (ball_subset_closedBall hx)

end OAI.Analysis.PDE.Dirichlet
