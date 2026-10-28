import OAI.Analysis.PDE.Concentration.WeakLaplacian

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory InnerProductSpace Laplacian Filter Set Metric
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A local C² function admits a globally C² representative on a smaller
neighborhood. No global regularity of the original function is required. -/
theorem exists_global_contDiff_two_eq_near {f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : E} (hx : x ∈ U) :
    ∃ F : E → ℝ, ∃ V : Set E, ContDiff ℝ 2 F ∧ IsOpen V ∧ x ∈ V ∧
      V ⊆ U ∧ EqOn F f V := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let b : ContDiffBump x :=
    { rIn := r / 4, rOut := r / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hs : tsupport b ⊆ U := by
    rw [b.tsupport_eq]
    intro y hy
    apply hball
    have hy' : dist y x ≤ r / 2 := hy
    exact lt_of_le_of_lt hy' (by linarith)
  refine ⟨fun y => b y * f y, ball x (r / 4), ?_, isOpen_ball, mem_ball_self (by positivity),
    ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport b
    · exact b.contDiffAt.mul ((hf y (hs hy)).contDiffAt (hU.mem_nhds (hs hy)))
    · apply (show ContDiffAt ℝ 2 (fun _ : E => (0 : ℝ)) y from contDiffAt_const).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp only [hz, Pi.zero_apply, zero_mul]
  · intro y hy
    exact hball (lt_trans (show dist y x < r / 4 from hy) (by linarith))
  · intro y hy
    dsimp only
    rw [b.one_of_mem_closedBall (show dist y x ≤ b.rIn from
      (show dist y x < r / 4 from hy).le), one_mul]

variable [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The weak upper Laplacian estimate is classical on the open domain
where the energy is C². This version does not assume smoothness across
the boundary of that domain. -/
theorem laplacian_le_of_weak_inequality_on {f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {δ : ℝ}
    (hweak : ∀ η : E → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U → (∀ x, 0 ≤ η x) →
      (∫ x, (Δ η) x * f x) ≤ δ * ∫ x, η x) :
    ∀ x ∈ U, Δ f x ≤ δ := by
  intro x hx
  obtain ⟨F, V, hF, hV, hxV, hVU, heq⟩ := exists_global_contDiff_two_eq_near hU hf hx
  have hbound : ∀ y ∈ V, Δ F y ≤ δ := laplacian_le_of_weak_inequality hF hV (by
    intro η hη hs hsV hn
    have he : (∫ y, Δ η y * F y) = ∫ y, Δ η y * f y := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ V
      · rw [heq hy]
      · have hys : y ∉ tsupport η := fun h => hy (hsV h)
        have hz : Δ η y = 0 := by
          rw [(laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp hys)).self_of_nhds]
          simp only [Pi.zero_def, laplacian_const, Pi.zero_apply]
        simp only [hz, zero_mul]
    rw [he]
    exact hweak η hη hs (hsV.trans hVU) hn)
  have he : F =ᶠ[𝓝 x] f := eventuallyEq_of_mem (hV.mem_nhds hxV) heq
  simpa only [(laplacian_congr_nhds he).self_of_nhds] using hbound x hxV

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)] in
theorem continuous_mul_of_support_inside {a g : E → ℝ} (ha : Continuous a)
    {U : Set E} (hU : IsOpen U) (hg : ContinuousOn g U) (hs : tsupport a ⊆ U) :
    Continuous (fun x => a x * g x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport a
  · exact ha.continuousAt.mul ((hg x (hs hx)).continuousAt (hU.mem_nhds (hs hx)))
  · apply (show ContinuousAt (fun _ : E => (0 : ℝ)) x from continuousAt_const).congr
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A weak Poisson identity and a pointwise forcing bound give the desired
upper Laplacian bound for the energy. The forcing need only be continuous
on the open domain. -/
theorem laplacian_le_of_weak_forcing_on {f g : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hg : ContinuousOn g U) {δ : ℝ}
    (hbound : ∀ x ∈ U, g x ≤ δ)
    (hweak : ∀ η : E → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U → (∫ x, Δ η x * f x) = ∫ x, η x * g x) :
    ∀ x ∈ U, Δ f x ≤ δ := by
  apply laplacian_le_of_weak_inequality_on hU hf
  intro η hη hs hsU hn
  rw [hweak η hη hs hsU]
  have hi : Integrable (fun x => η x * g x) :=
    (continuous_mul_of_support_inside hη.continuous hU hg hsU).integrable_of_hasCompactSupport
      hs.mul_right
  have hc : Integrable (fun x => η x * δ) :=
    (hη.continuous.mul continuous_const).integrable_of_hasCompactSupport hs.mul_right
  calc
    _ ≤ ∫ x, η x * δ := integral_mono hi hc (fun x => by
      by_cases hx : x ∈ tsupport η
      · exact mul_le_mul_of_nonneg_left (hbound x (hsU hx)) (hn x)
      · have hz : η x = 0 := by
          by_contra h
          exact hx (subset_tsupport η h)
        simp only [hz, zero_mul, le_refl])
    _ = _ := by rw [integral_mul_const, mul_comm]

end OAI.Analysis.PDE.Concentration
