import OAI.Analysis.PDE.Nonlinear.Freeze

/-! One localization scale works for all sufficiently small finite differences. -/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

theorem exists_uniform_small_localized_family
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α ε ρ M : ℝ} (hα : 0 < α) (hα1 : α < 1) (hε : 0 < ε) (hρ : 0 < ρ)
    (hM : 0 ≤ M) (A : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (a : F) (x₀ : E)
    (hA : ∀ h, ‖A h‖ ≤ M)
    (hlim : Tendsto (fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x₀) (𝓝 0) (𝓝 a)) :
    ∃ r > 0, r < ρ ∧ ∃ δ > 0, ∀ h, |h| < δ →
      ∃ B : OAI.Analysis.Normed.Function.Holder.HolderMap E F α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = OAI.Analysis.PDE.Schauder.radialCutoff 1 x • (a - OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) (x₀ + r • x))) ∧
        ‖B‖ < ε ∧ (∀ x, x ∉ closedBall 0 2 → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0) := by
  obtain ⟨C, hC, hc⟩ := exists_localized_offset_holder (E := E) (F := F) hα.le hα1.le
  obtain ⟨r, hr, hrρ, hrsmall⟩ := OAI.Analysis.PDE.Schauder.exists_small_positive_rpow_mul hα
    (mul_nonneg hC.le hM) (half_pos hε) hρ
  have het : 0 < ε / (2 * C) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.tendsto_nhds_nhds.mp hlim (ε / (2 * C)) het
  refine ⟨r, hr, hrρ, δ, hδ, ?_⟩
  intro h hh
  obtain ⟨B, hv, hb, hs⟩ := hc (A h) a x₀ r hr.le
  refine ⟨B, hv, ?_, hs⟩
  have hoff : ‖a - OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x₀‖ < ε / (2 * C) := by
    have hh' : dist h (0 : ℝ) < δ := by simpa only [Real.dist_eq, sub_zero] using hh
    simpa only [dist_eq_norm, norm_sub_rev] using hδsmall hh'
  have hmul : C * ‖a - OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x₀‖ < ε / 2 := by
    have hm := mul_lt_mul_of_pos_left hoff hC
    have heq : C * (ε / (2 * C)) = ε / 2 := by field_simp
    rwa [heq] at hm
  have hmain : C * (‖A h‖ * r ^ α) < ε / 2 :=
    lt_of_le_of_lt (by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA h) hC.le)
        (Real.rpow_nonneg hr.le _)) hrsmall
  exact hb.trans_lt (by linarith only [hmain, hmul])

end OAI.Analysis.PDE.Nonlinear
