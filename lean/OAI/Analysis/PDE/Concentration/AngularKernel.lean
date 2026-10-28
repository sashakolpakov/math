import OAI.Analysis.PDE.Concentration.GaussianKernel
import OAI.Analysis.PDE.Concentration.KernelScale
import OAI.Analysis.PDE.Concentration.RotatedKernel

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set
open scoped ContDiff
open OAI.Analysis.Calculus.Current

/-- The source uses angular frequencies. In the cycles Fourier convention
its multiplier `b(h D)` has inverse kernel at scale `2πh`. -/
theorem gaussianForwardAngularKernel_bound {d : ℕ} (j : Fin 2) {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (w₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ w₀ →
      ∀ h : ℝ, 0 < h → ∀ L : ℝ, 1 ≤ L → ∀ x,
      ‖scaledInverseKernel (gaussianForwardSymbol j ρ χ h L W) (2 * Real.pi * h) x‖ ≤
        (C * (h ^ d)⁻¹ * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 - d / 2)) *
          OAI.Analysis.Calculus.Current.smoothingKernel d h x := by
  obtain ⟨A, hA, ha⟩ := gaussianForwardKernel_bound_at_scale j hρ hcρ hχ hcχ hpos w₀
  refine ⟨A * (2 * Real.pi) ^ (2 * (d + 3)), by positivity, ?_⟩
  intro W hW h hh L hL x
  have hb := ha W hW h hh L hL (2 * Real.pi * h) (by positivity) x
  apply hb.trans
  have hc := mul_le_mul_of_nonneg_left (smoothingKernel_two_pi hh x)
    (show 0 ≤ A * (h ^ d)⁻¹ * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 - d / 2) by positivity)
  convert hc using 1 ; ring

theorem gaussianInverseAngularKernel_bound {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ tsupport ρ, ‖gaussianVelocity η‖ ≤ 1)
    (Rχ RW : ℝ) (hsupp : tsupport χ ⊆ Metric.closedBall 0 Rχ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ 1 →
      ∀ h : ℝ, 0 < h → ∀ L : ℝ, 1 ≤ L → Real.sqrt L * ‖W‖ ≤ RW → ∀ x,
      ‖scaledInverseKernel (gaussianInverseSymbol ρ χ h L W) (2 * Real.pi * h) x‖ ≤
        (C * h ^ d * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 + d / 2)) *
          OAI.Analysis.Calculus.Current.smoothingKernel d h x := by
  obtain ⟨A, hA, ha⟩ := gaussianInverseKernel_bound_at_scale hρ hcρ hχ hcχ hpos hv Rχ RW hsupp
  refine ⟨A * (2 * Real.pi) ^ (2 * (d + 3)), by positivity, ?_⟩
  intro W hW h hh L hL hRW x
  have hb := ha W hW h hh L hL hRW (2 * Real.pi * h) (by positivity) x
  apply hb.trans
  have hc := mul_le_mul_of_nonneg_left (smoothingKernel_two_pi hh x)
    (show 0 ≤ A * h ^ d * L ^ (((gaussianDerivativeOrder d : ℕ) : ℝ) / 2 + d / 2) by positivity)
  convert hc using 1 ; ring

end OAI.Analysis.PDE.Concentration
