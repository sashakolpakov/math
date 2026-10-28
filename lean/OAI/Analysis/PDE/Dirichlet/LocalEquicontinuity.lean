import OAI.Analysis.PDE.Dirichlet.JetCompactness

open Set Metric Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

theorem equicontinuous_of_local_holder {E Y ι : Type*}
    [PseudoMetricSpace E] [NormedAddCommGroup Y] {u : ι → E → Y}
    (hlocal : ∀ x₀, ∃ r α C : ℝ, 0 < r ∧ 0 < α ∧
      ∀ i x, dist x x₀ < r → ‖u i x₀ - u i x‖ ≤ C * dist x₀ x ^ α) :
    Equicontinuous u := by
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨r, α, C, hr, hα, hbound⟩ := hlocal x₀
  have ht : Tendsto (fun d : ℝ ↦ C * d ^ α) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow hα.ne'] using
      (show Continuous (fun d : ℝ ↦ C * d ^ α) from
        continuous_const.mul (Real.continuous_rpow_const hα.le)).tendsto 0
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp (ht (Iio_mem_nhds hε))
  refine ⟨min r δ, lt_min hr hδ, ?_⟩
  intro x hx i
  have hd : dist x₀ x ∈ ball (0 : ℝ) δ := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg dist_nonneg,
      dist_comm x₀ x] using hx.trans_le (min_le_right r δ)
  have hb : dist (u i x₀) (u i x) ≤ C * dist x₀ x ^ α := by
    simpa only [dist_eq_norm] using hbound i x (hx.trans_le (min_le_left r δ))
  exact hb.trans_lt (hsmall hd)

theorem equicontinuous_restrict_of_open_fderiv_bound
    {E Y ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Ω : Set E} (hΩ : IsOpen Ω) {u : ι → E → Y} {M : ℝ}
    (hu : ∀ i x, x ∈ Ω → DifferentiableAt ℝ (u i) x)
    (hbound : ∀ i x, x ∈ Ω → ‖fderiv ℝ (u i) x‖ ≤ M) :
    Equicontinuous (fun i (x : Ω) ↦ u i x) := by
  apply equicontinuous_of_local_holder
  intro x₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ x₀.property
  refine ⟨r, 1, M, hr, zero_lt_one, ?_⟩
  intro i x hx
  have hx' : (x : E) ∈ ball (x₀ : E) r := hx
  have hx₀ : (x₀ : E) ∈ ball (x₀ : E) r := mem_ball_self hr
  have hb := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ hu i z (hball hz)) (fun z hz ↦ hbound i z (hball hz))
    (convex_ball (x₀ : E) r) hx' hx₀
  simpa only [Real.rpow_one, Subtype.dist_eq, dist_eq_norm] using hb

theorem equicontinuous_restrict_of_compact_holder
    {E Y ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup Y] {Ω : Set E} (hΩ : IsOpen Ω) {u : ι → E → Y}
    (hholder : ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ α C : ℝ, 0 < α ∧
      ∀ i x, x ∈ K → ∀ y, y ∈ K → ‖u i x - u i y‖ ≤ C * dist x y ^ α) :
    Equicontinuous (fun i (x : Ω) ↦ u i x) := by
  apply equicontinuous_of_local_holder
  intro x₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ x₀.property
  have hh : 0 < r / 2 := by positivity
  have hKΩ : closedBall (x₀ : E) (r / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith : r / 2 < r)).trans hball
  obtain ⟨α, C, hα, hC⟩ := hholder _ (isCompact_closedBall _ _) hKΩ
  refine ⟨r / 2, α, C, hh, hα, ?_⟩
  intro i x hx
  exact hC i x₀ (mem_closedBall_self hh.le) x (mem_closedBall.mpr hx.le)

end OAI.Analysis.PDE.Dirichlet
