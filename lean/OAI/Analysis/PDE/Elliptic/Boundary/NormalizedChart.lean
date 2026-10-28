import OAI.Analysis.PDE.Elliptic.Boundary.Normal
import OAI.Analysis.PDE.Elliptic.Boundary.LocalExtension

/-! Normalized globally smooth charts agreeing with the actual local IFT
chart near the closed unit ball, with image in any prescribed neighborhood. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_doubled_boundary_chart {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (x : E) (hg : fderiv ℝ r x ≠ 0) {U : Set E} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (v : E) (c : ℝ) (G P : E → E), ‖v‖ = 1 ∧ 0 < c ∧
      ContDiff ℝ 3 G ∧ ContDiff ℝ 3 P ∧ G 0 = x ∧
      ∀ z ∈ Metric.closedBall 0 2,
        G z ∈ U ∧ (fun y => P (G y)) =ᶠ[𝓝 z] id ∧
        r (G z) - r x = -c * inner ℝ v z := by
  obtain ⟨v, c0, hv, hc0, hnormal⟩ := exists_inward_unit_normal (fderiv ℝ r x) hg
  obtain ⟨w, F, R, hR, hw, hF0, hDF, hF, hright, hlevel⟩ := exists_boundary_flattening hr x hg
  have hFU : ∀ᶠ y in 𝓝 (0 : E), F y ∈ U := by
    have hh := hDF.continuousAt.tendsto.eventually (hU.mem_nhds (show F 0 ∈ U by simpa [hF0]))
    exact hh
  have hgood : ∀ᶠ y in 𝓝 (0 : E), y ∈ Metric.ball 0 R ∧ F y ∈ U :=
    Filter.Eventually.and (Metric.ball_mem_nhds (0 : E) hR) hFU
  obtain ⟨ε, hε, heps⟩ := Metric.mem_nhds_iff.mp hgood
  let ρ := ε / 8
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let S : E → E := fun z => F (ρ • z)
  let P : E → E := fun y => ρ⁻¹ • flatteningMap r x (fderiv ℝ r x) w y
  have hscaled (z : E) (hz : ‖z‖ ≤ 4) : ρ • z ∈ Metric.ball (0 : E) ε := by
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    dsimp [ρ]
    nlinarith
  have hinR (z : E) (hz : ‖z‖ ≤ 4) : ρ • z ∈ Metric.closedBall (0 : E) R :=
    Metric.ball_subset_closedBall (heps (hscaled z hz)).1
  have hS (z : E) (hz : z ∈ Metric.closedBall (0 : E) 2) : ContDiffAt ℝ 3 S z := by
    have hz' : ‖z‖ ≤ 4 := by have := Metric.mem_closedBall.mp hz; simp only [dist_zero_right] at this; linarith
    exact (hF _ (hinR z hz')).comp z (contDiffAt_const.smul contDiffAt_id)
  obtain ⟨G, hG, hGS⟩ := exists_contDiff_extension_near_compact (k := 3) (isCompact_closedBall (0 : E) 2)
    (fun z hz => by simpa using hS z hz)
  have hG0 : G 0 = x := by
    rw [(hGS 0 (by simp)).eq_of_nhds]
    simpa [S] using hF0
  have hP : ContDiff ℝ 3 P := contDiff_const.smul (contDiff_flatteningMap hr x _ w)
  refine ⟨v, ρ * c0, G, P, hv, mul_pos hρ hc0, by simpa using hG, hP, hG0, ?_⟩
  intro z hz
  have hz1 : ‖z‖ ≤ 2 := by simpa using hz
  have hGSz := (hGS z hz).eq_of_nhds
  refine ⟨?_, ?_, ?_⟩
  · rw [hGSz]
    exact (heps (hscaled z (by linarith))).2
  · have hznear : z ∈ Metric.ball (0 : E) 4 := by simpa using (show ‖z‖ < 4 by linarith)
    filter_upwards [hGS z hz, Metric.isOpen_ball.mem_nhds hznear] with y hy hyball
    rw [hy]
    have hnorm : ‖y‖ ≤ 4 := by have := Metric.mem_ball.mp hyball; simp only [dist_zero_right] at this; exact this.le
    change ρ⁻¹ • flatteningMap r x (fderiv ℝ r x) w (F (ρ • y)) = y
    rw [hright _ (hinR y hnorm), smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
  · rw [hGSz]
    change r (F (ρ • z)) - r x = _
    rw [hlevel _ (hinR z (by linarith)), hnormal]
    simp only [real_inner_smul_right]
    ring

theorem exists_normalized_boundary_chart {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (x : E) (hg : fderiv ℝ r x ≠ 0) {U : Set E} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (v : E) (c : ℝ) (G P : E → E), ‖v‖ = 1 ∧ 0 < c ∧
      ContDiff ℝ 3 G ∧ ContDiff ℝ 3 P ∧ G 0 = x ∧
      ∀ z ∈ Metric.closedBall 0 1,
        G z ∈ U ∧ (fun y => P (G y)) =ᶠ[𝓝 z] id ∧
        r (G z) - r x = -c * inner ℝ v z := by
  obtain ⟨v, c, G, P, hv, hc, hG, hP, hG0, hchart⟩ := exists_doubled_boundary_chart hr x hg hU hxU
  exact ⟨v, c, G, P, hv, hc, hG, hP, hG0, fun z hz =>
    hchart z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz)⟩

end OAI.Analysis.PDE.Elliptic
