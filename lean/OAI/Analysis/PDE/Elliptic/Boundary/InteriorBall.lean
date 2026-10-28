import Mathlib

/-! Fixed-data interior balls at depth h. The radius is proportional to h,
uniformly over a compact set of centers, and follows from the actual C¹
defining function rather than an assumed geometric ball condition. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric

theorem exists_uniform_sublevel_balls
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {r : E → ℝ} (hr : ContDiff ℝ 1 r) {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {c : ℝ} (hc : 0 < c) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
      ∀ x ∈ K, ∀ h : ℝ, 0 < h → h ≤ 1 → r x = -c * h →
        closedBall x (κ * h) ⊆ U ∩ {y | r y < 0} := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hKδ : IsCompact (cthickening δ K) := hK.cthickening
  have hDr : Continuous (fderiv ℝ r) := (hr.fderiv_right (m := 0) (by norm_num)).continuous
  obtain ⟨D₀, hD₀⟩ := hKδ.exists_bound_of_continuousOn hDr.continuousOn
  let D := max D₀ 0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hD₀D : D₀ ≤ D := by dsimp [D]; linarith [le_max_left D₀ 0]
  let κ := min 1 (min δ (c / (2 * D)))
  have hκ : 0 < κ := lt_min zero_lt_one (lt_min hδ (div_pos hc (by positivity)))
  have hκδ : κ ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hκc : κ ≤ c / (2 * D) := (min_le_right _ _).trans (min_le_right _ _)
  have hDκ : D * κ ≤ c / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * D by positivity)).mp hκc
    nlinarith
  refine ⟨κ, hκ, min_le_left _ _, ?_⟩
  intro x hx h hh hh1 hrx y hy
  have hradius : κ * h ≤ δ := (mul_le_of_le_one_right hκ.le hh1).trans hκδ
  have hyδ : y ∈ closedBall x δ := closedBall_subset_closedBall hradius hy
  have hsubset : closedBall x δ ⊆ cthickening δ K := closedBall_subset_cthickening hx δ
  refine ⟨hδU (hsubset hyδ), ?_⟩
  have hdiff := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ closedBall x δ) => hr.differentiable (by norm_num) z)
    (fun z hz => (hD₀ z (hsubset hz)).trans hD₀D) (convex_closedBall x δ)
    (mem_closedBall_self hδ.le) hyδ
  have hxy : ‖y - x‖ ≤ κ * h := by simpa only [mem_closedBall, dist_eq_norm] using hy
  have hybound : r y - r x ≤ D * (κ * h) :=
    (le_abs_self _).trans (hdiff.trans (mul_le_mul_of_nonneg_left hxy hD.le))
  have hprod := mul_le_mul_of_nonneg_right hDκ hh.le
  rw [hrx] at hybound
  change r y < 0
  nlinarith [mul_pos hc hh]

end OAI.Analysis.PDE.Elliptic
