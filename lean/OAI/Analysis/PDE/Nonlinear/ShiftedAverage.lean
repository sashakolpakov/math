import OAI.Analysis.PDE.Nonlinear.AverageSmall
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HolderPullback

/-! Uniform actual averaged coefficients for finite differences of a Hölder field. -/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

theorem exists_shifted_average_family
    {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) (hg : ContDiff ℝ 1 g) {α : ℝ} (hα : 0 < α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (v : X) :
    ∃ A : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap X F α,
      (∀ h x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x =
        segmentAverage g (OAI.Analysis.Normed.Function.Holder.HolderMap.value H x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value H (x + h • v))) ∧
      (∃ M ≥ 0, ∀ h, ‖A h‖ ≤ M) ∧
      (∀ x, Tendsto (fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x) (𝓝 0) (𝓝 (g (OAI.Analysis.Normed.Function.Holder.HolderMap.value H x)))) := by
  let T (h : ℝ) : OAI.Analysis.Normed.Function.Holder.HolderMap X E α := OAI.Analysis.PDE.Schauder.holderIsometricPullback hα.le
    (fun x => x + h • v) (isometry_iff_dist_eq.mpr (fun x y => dist_add_right x y (h • v))) H
  have hT (h : ℝ) : ‖T h‖ ≤ ‖H‖ :=
    OAI.Analysis.PDE.Schauder.norm_holderIsometricPullback_le hα.le _ _ H
  obtain ⟨C, hC, hc⟩ := exists_segmentAverage_holder_bound (X := X) g hg hα (norm_nonneg H)
  have hex (h : ℝ) := hc H (T h) le_rfl (hT h)
  choose A hAval hAnorm using hex
  have hval (h : ℝ) (x : X) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x =
      segmentAverage g (OAI.Analysis.Normed.Function.Holder.HolderMap.value H x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value H (x + h • v)) := hAval h x
  refine ⟨A, hval, ⟨C * (1 + 2 * ‖H‖), by positivity, ?_⟩, ?_⟩
  · intro h
    exact (hAnorm h).trans (mul_le_mul_of_nonneg_left (by linarith only [hT h]) hC)
  · intro x
    obtain ⟨L, hLip⟩ := hg.contDiffOn.exists_lipschitzOnWith (by norm_num)
      (convex_closedBall (0 : E) ‖H‖) (isCompact_closedBall (0 : E) ‖H‖)
    have hLip' (a : E) (ha : ‖a‖ ≤ ‖H‖) (b : E) (hb : ‖b‖ ≤ ‖H‖) :
        ‖g a - g b‖ ≤ (L : ℝ) * ‖a - b‖ := by
      have hh := hLip.dist_le_mul a (by simpa only [mem_closedBall, dist_zero_right] using ha)
        b (by simpa only [mem_closedBall, dist_zero_right] using hb)
      simpa only [dist_eq_norm] using hh
    have hlim : Tendsto (fun h : ℝ => OAI.Analysis.Normed.Function.Holder.HolderMap.value H (x + h • v)) (𝓝 0)
        (𝓝 (OAI.Analysis.Normed.Function.Holder.HolderMap.value H x)) := by
      have hp : Continuous (fun h : ℝ => x + h • v) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hcH : Continuous (OAI.Analysis.Normed.Function.Holder.HolderMap.value H) := H.val.1.continuous
      simpa only [Function.comp_def, zero_smul, add_zero] using (hcH.comp hp).tendsto 0
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hpos : 0 < ε / ((L : ℝ) + 1) := div_pos hε (by positivity)
    have hev := Metric.tendsto_nhds.mp hlim (ε / ((L : ℝ) + 1)) hpos
    filter_upwards [hev] with h hh
    rw [hval, dist_eq_norm, ← segmentAverage_self g (OAI.Analysis.Normed.Function.Holder.HolderMap.value H x)]
    have hb := segmentAverage_sub_le g hg.continuous L.coe_nonneg hLip'
      (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le H x) (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le H (x + h • v))
      (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le H x) (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le H x)
    simp only [sub_self, norm_zero, zero_add] at hb
    apply hb.trans_lt
    have hh' : ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value H (x + h • v) - OAI.Analysis.Normed.Function.Holder.HolderMap.value H x‖ < ε / ((L : ℝ) + 1) := by
      simpa only [dist_eq_norm] using hh
    calc
      (L : ℝ) * ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value H (x + h • v) - OAI.Analysis.Normed.Function.Holder.HolderMap.value H x‖ ≤
          ((L : ℝ) + 1) * ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value H (x + h • v) - OAI.Analysis.Normed.Function.Holder.HolderMap.value H x‖ := by
        nlinarith only [norm_nonneg (OAI.Analysis.Normed.Function.Holder.HolderMap.value H (x + h • v) - OAI.Analysis.Normed.Function.Holder.HolderMap.value H x)]
      _ < ((L : ℝ) + 1) * (ε / ((L : ℝ) + 1)) :=
        mul_lt_mul_of_pos_left hh' (by positivity)
      _ = ε := mul_div_cancel₀ ε (by positivity)

end OAI.Analysis.PDE.Nonlinear
