import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothMetricLocalization

/-! # Smooth Frozen Extension -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SmoothFrozenExtension.Constructions

noncomputable section

/-! A smooth coefficient field has a bounded Lipschitz extension near any
interior point, uniformly close to its value at that point. -/

open Set _root_.Metric
open scoped ContDiff _root_.Topology
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothMetricLocalization.CM.Construction

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_smooth_frozen_extension {U : Set E} (hU : IsOpen U)
    (A : E → G) (hA : ContDiffOn ℝ ∞ A U) {z : E} (hz : z ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : E → G, B =ᶠ[𝓝 z] A ∧ ContDiff ℝ ∞ B ∧
      HasCompactSupport (fun x => B x - A z) ∧
      (∀ x, ‖B x - A z‖ ≤ ε) ∧
      (∃ C : ℝ, ∀ x, ‖B x‖ ≤ C) ∧ (∃ L : NNReal, LipschitzWith L B) := by
  have hcont : ContinuousAt (fun x => ‖A x - A z‖) z :=
    (((hA.contDiffAt (hU.mem_nhds hz)).continuousAt).sub continuousAt_const).norm
  have hsmall : ∀ᶠ x in 𝓝 z, ‖A x - A z‖ < ε :=
    hcont.eventually (gt_mem_nhds (by simpa only [sub_self, norm_zero] using hε))
  have hUe : ∀ᶠ x in 𝓝 z, x ∈ U := hU.mem_nhds hz
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hUe.and hsmall)
  obtain ⟨η, hη, hηc, hηball, hη₀, hη₁, hηz⟩ :=
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothMetricLocalization.CM.Construction.exists_smooth_local_cutoff (U := ball z r) isOpen_ball (mem_ball_self hr)
  have hηU : tsupport η ⊆ U := fun x hx => (hball ((mem_ball).mp (hηball hx))).1
  let B := fun x => A z + η x • (A x - A z)
  have hB : ContDiff ℝ ∞ B := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact contDiffAt_const.add (hη.contDiffAt.smul
        ((hA.contDiffAt (hU.mem_nhds hx)).sub contDiffAt_const))
    · have hzero : η =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hηU h))
      have heq : B =ᶠ[𝓝 x] (fun _ => A z) := by
        filter_upwards [hzero] with y hy
        simp only [B, hy, Pi.zero_apply, zero_smul, add_zero]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  have hBc : HasCompactSupport (fun x => B x - A z) := by
    apply hηc.mono'
    intro x hx
    by_contra hn
    exact hx (by simp only [B, image_eq_zero_of_notMem_tsupport hn, zero_smul, add_zero, sub_self])
  have hclose (x : E) : ‖B x - A z‖ ≤ ε := by
    by_cases hx : x ∈ tsupport η
    · have hs := (hball ((mem_ball).mp (hηball hx))).2.le
      have hηnorm : ‖η x‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (hη₀ x)]; exact hη₁ x
      calc
        _ = ‖η x‖ * ‖A x - A z‖ := by
          dsimp [B]
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * ε := mul_le_mul hηnorm hs (norm_nonneg _) (by norm_num)
        _ = ε := one_mul ε
    · simp only [B, image_eq_zero_of_notMem_tsupport hx, zero_smul, add_zero, sub_self, norm_zero]
      exact hε.le
  refine ⟨B, ?_, hB, hBc, hclose, ⟨‖A z‖ + ε, fun x => ?_⟩, ?_⟩
  · filter_upwards [hηz] with x hx
    simp only [B, hx, Pi.one_apply, one_smul, add_sub_cancel]
  · calc
      _ ≤ ‖A z‖ + ‖B x - A z‖ := by
        simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub (A z) (B x)
      _ ≤ _ := add_le_add le_rfl (hclose x)
  · obtain ⟨L, hL⟩ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothCoefficientExtension.CM.Construction.compact_smooth_lipschitz (fun x => B x - A z) (hB.sub contDiff_const) hBc
    refine ⟨L, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hL.dist_le_mul x y

end

end OAI.Analysis.HodgeTheory.Decomposition.SmoothFrozenExtension.Constructions
