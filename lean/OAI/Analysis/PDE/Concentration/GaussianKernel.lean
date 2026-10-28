import OAI.Analysis.PDE.Concentration.SymbolNormalization
import OAI.Analysis.PDE.Concentration.Periodized

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory
open scoped ContDiff
open OAI.Analysis.Calculus.Current

def gaussianDerivativeOrder (d : ℕ) : ℕ := 2 * (d + 3)

theorem tsupport_gaussianForwardSymbol {d : ℕ} (j : Fin 2) (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ)
    (χ : TransverseSpace d → ℂ) (h L : ℝ) (W : TransverseSpace d) :
    tsupport (gaussianForwardSymbol j ρ χ h L W) ⊆ tsupport ρ := by
  apply closure_minimal _ (isClosed_tsupport ρ)
  intro η hη
  by_contra hn
  have hz : ρ η = 0 := (notMem_tsupport_iff_eventuallyEq.mp hn).self_of_nhds
  apply hη
  simp [gaussianForwardSymbol, gaussianForwardCore, radialAngularCutoff, hz]

theorem tsupport_gaussianInverseSymbol {d : ℕ} (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ)
    (χ : TransverseSpace d → ℂ) (h L : ℝ) (W : TransverseSpace d) :
    tsupport (gaussianInverseSymbol ρ χ h L W) ⊆ tsupport ρ := by
  apply closure_minimal _ (isClosed_tsupport ρ)
  intro η hη
  by_contra hn
  have hz : ρ η = 0 := (notMem_tsupport_iff_eventuallyEq.mp hn).self_of_nhds
  apply hη
  simp [gaussianInverseSymbol, gaussianInverseCore, radialAngularCutoff, hz]

theorem finite_order_smoothing_majorant {d : ℕ} {S : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)} (hS : IsCompact S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (b : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (B h : ℝ),
      ContDiff ℝ (2 * (d + 3) : ℕ) b → tsupport b ⊆ S → 0 ≤ B →
      (∀ j ≤ 2 * (d + 3), ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ B) → 0 < h →
      ∀ x, ‖scaledInverseKernel b h x‖ ≤ K * B * OAI.Analysis.Calculus.Current.smoothingKernel d h x := by
  let K := (2 ^ (2 * (d + 3)) * (1 + 2 ^ (2 * (d + 3)) * (2 * (d + 3) + 1)) *
    volume.real S) / OAI.Analysis.Calculus.Current.kernelConstant d
  refine ⟨K, div_nonneg (by positivity) (OAI.Analysis.Calculus.Current.kernelConstant_pos d).le, ?_⟩
  intro b B h hb hs hB hd hh x
  exact finite_order_kernel_le_smoothing hS hb hs hB hd hh x

/-- The actual forward multiplier kernel is dominated by the probability
smoothing kernel, with the source's fixed logarithmic loss. -/
theorem gaussianForwardKernel_bound_at_scale {d : ℕ} (j : Fin 2) {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (w₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ w₀ →
      ∀ h : ℝ, 0 < h → ∀ L : ℝ, 1 ≤ L → ∀ r : ℝ, 0 < r → ∀ x,
      ‖scaledInverseKernel (gaussianForwardSymbol j ρ χ h L W) r x‖ ≤
        (C * (h ^ d)⁻¹ * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 - d / 2)) *
          OAI.Analysis.Calculus.Current.smoothingKernel d r x := by
  obtain ⟨A, hA, ha⟩ := gaussianForwardSymbol_jets j hρ hcρ hχ hcχ hpos w₀ (gaussianDerivativeOrder d)
  obtain ⟨K, hK, hk⟩ := finite_order_smoothing_majorant hcρ
  refine ⟨K * A, mul_nonneg hK hA, ?_⟩
  intro W hW h hh L hL r hr x
  let B := A * (h ^ d)⁻¹ * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 - d / 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hderiv : ∀ n ≤ 2 * (d + 3), ∀ η,
      ‖iteratedFDeriv ℝ n (gaussianForwardSymbol j ρ χ h L W) η‖ ≤ B := by
    intro n hn η
    have hnM : n ≤ gaussianDerivativeOrder d := by dsimp [gaussianDerivativeOrder]; omega
    apply (ha W hW h hh L hL n hnM η).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hL
    have hc : (n : ℝ) ≤ gaussianDerivativeOrder d := by exact_mod_cast hnM
    linarith
  have hsmooth : ContDiff ℝ (2 * (d + 3) : ℕ) (gaussianForwardSymbol j ρ χ h L W) := by
    unfold gaussianForwardSymbol
    exact ((contDiff_gaussianForwardCore j hρ hχ hpos (L := L) (by linarith) W).const_smul
      ((h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2))).of_le
      (WithTop.coe_le_coe.mpr (le_top : ((2 * (d + 3) : ℕ) : ℕ∞) ≤ ⊤))
  have hb := hk _ B r hsmooth (tsupport_gaussianForwardSymbol j ρ χ h L W) hB hderiv hr x
  simpa only [B, mul_assoc] using hb

theorem gaussianInverseKernel_bound_at_scale {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ tsupport ρ, ‖gaussianVelocity η‖ ≤ 1)
    (Rχ RW : ℝ) (hsupp : tsupport χ ⊆ Metric.closedBall 0 Rχ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ 1 →
      ∀ h : ℝ, 0 < h → ∀ L : ℝ, 1 ≤ L → Real.sqrt L * ‖W‖ ≤ RW → ∀ r : ℝ, 0 < r → ∀ x,
      ‖scaledInverseKernel (gaussianInverseSymbol ρ χ h L W) r x‖ ≤
        (C * h ^ d * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 + d / 2)) *
          OAI.Analysis.Calculus.Current.smoothingKernel d r x := by
  obtain ⟨A, hA, ha⟩ := gaussianInverseSymbol_jets hρ hcρ hχ hcχ hpos hv Rχ RW hsupp (gaussianDerivativeOrder d)
  obtain ⟨K, hK, hk⟩ := finite_order_smoothing_majorant hcρ
  refine ⟨K * A, mul_nonneg hK hA, ?_⟩
  intro W hW h hh L hL hRW r hr x
  let B := A * h ^ d * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 + d / 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hderiv : ∀ n ≤ 2 * (d + 3), ∀ η,
      ‖iteratedFDeriv ℝ n (gaussianInverseSymbol ρ χ h L W) η‖ ≤ B := by
    intro n hn η
    have hnM : n ≤ gaussianDerivativeOrder d := by dsimp [gaussianDerivativeOrder]; omega
    apply (ha W hW h hh L hL hRW n hnM η).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hL
    have hc : (n : ℝ) ≤ gaussianDerivativeOrder d := by exact_mod_cast hnM
    linarith
  have hsmooth : ContDiff ℝ (2 * (d + 3) : ℕ) (gaussianInverseSymbol ρ χ h L W) := by
    unfold gaussianInverseSymbol
    exact ((contDiff_gaussianInverseCore hρ hχ hpos hv (L := L) (by linarith) W hW).const_smul
      (h ^ d * L ^ ((d : ℝ) / 2))).of_le
      (WithTop.coe_le_coe.mpr (le_top : ((2 * (d + 3) : ℕ) : ℕ∞) ≤ ⊤))
  have hb := hk _ B r hsmooth (tsupport_gaussianInverseSymbol ρ χ h L W) hB hderiv hr x
  simpa only [B, mul_assoc] using hb

end OAI.Analysis.PDE.Concentration
