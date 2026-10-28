import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Freeze

/-! Freezing a family at one fixed coefficient, allowing a small constant offset. -/

noncomputable section
open Set Metric
open scoped Topology BoundedContinuousFunction
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

theorem exists_localized_offset_holder
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (a : F) (x₀ : E) (r : ℝ), 0 ≤ r →
      ∃ B : OAI.Analysis.Normed.Function.Holder.HolderMap E F α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = OAI.Analysis.PDE.Schauder.radialCutoff 1 x • (a - OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + r • x))) ∧
        ‖B‖ ≤ C * (‖f‖ * r ^ α + ‖a - OAI.Analysis.Normed.Function.Holder.HolderMap.value f x₀‖) ∧
        (∀ x, x ∉ closedBall 0 2 → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0) := by
  obtain ⟨C₀, hC₀, hc⟩ := OAI.Analysis.PDE.Schauder.exists_localized_difference_holder (E := E) (F := F) hα hα1
  let χ : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α := OAI.Analysis.PDE.Schauder.compactC1Holder (OAI.Analysis.PDE.Schauder.radialCutoff 1)
    ((OAI.Analysis.PDE.Schauder.contDiff_radialCutoff 1).of_le (by simp))
    (OAI.Analysis.PDE.Schauder.hasCompactSupport_radialCutoff zero_lt_one) hα hα1
  let C := C₀ + ‖χ‖ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f a x₀ r hr
  obtain ⟨B₀, hval, hb, hs⟩ := hc f x₀ r hr
  let d := a - OAI.Analysis.Normed.Function.Holder.HolderMap.value f x₀
  let L : ℝ →L[ℝ] F := (ContinuousLinearMap.id ℝ ℝ).smulRight d
  let D : OAI.Analysis.Normed.Function.Holder.HolderMap E F α := OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM L χ
  have hDval (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = OAI.Analysis.PDE.Schauder.radialCutoff 1 x • d := rfl
  have hL : ‖L‖ ≤ ‖d‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg d)
    intro t
    change ‖t • d‖ ≤ ‖d‖ * ‖t‖
    rw [norm_smul, mul_comm]
  have hD : ‖D‖ ≤ ‖χ‖ * ‖d‖ := by
    calc
      _ ≤ ‖L‖ * ‖χ‖ := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le L χ
      _ ≤ ‖d‖ * ‖χ‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg χ)
      _ = _ := mul_comm _ _
  refine ⟨B₀ + D, ?_, ?_, ?_⟩
  · intro x
    change OAI.Analysis.Normed.Function.Holder.HolderMap.value B₀ x + OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = _
    rw [hval, hDval, ← smul_add]
    congr 1
    dsimp only [OAI.Analysis.PDE.Schauder.dilatedDifference, d]
    abel
  · have hpow : 0 ≤ ‖f‖ * r ^ α := mul_nonneg (norm_nonneg f) (Real.rpow_nonneg hr _)
    calc
      _ ≤ ‖B₀‖ + ‖D‖ := norm_add_le _ _
      _ ≤ C₀ * ‖f‖ * r ^ α + ‖χ‖ * ‖d‖ := add_le_add hb hD
      _ ≤ C * (‖f‖ * r ^ α + ‖d‖) := by
        dsimp only [C]
        nlinarith only [hC₀.le, norm_nonneg χ, norm_nonneg d, hpow,
          mul_nonneg (norm_nonneg χ) hpow, mul_nonneg hC₀.le (norm_nonneg d)]
  · intro x hx
    change OAI.Analysis.Normed.Function.Holder.HolderMap.value B₀ x + OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = 0
    rw [hs x hx, hDval]
    have hx2 : 2 < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hx
    rw [OAI.Analysis.PDE.Schauder.radialCutoff_zero zero_lt_one (by linarith), zero_smul, add_zero]

end OAI.Analysis.PDE.Nonlinear
