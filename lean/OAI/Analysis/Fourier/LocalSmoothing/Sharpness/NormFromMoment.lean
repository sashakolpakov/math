import Mathlib

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open _root_.MeasureTheory
open scoped ENNReal

theorem norm_lower_of_moment {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : AEStronglyMeasurable f μ)
    {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (h : ENNReal.ofReal C ≤ ∫⁻ x, ‖f x‖ₑ^p ∂μ) :
    ENNReal.ofReal (C^(1/p)) ≤ eLpNorm f (ENNReal.ofReal p) μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le,←ENNReal.ofReal_rpow_of_nonneg hC (by positivity)]
  exact ENNReal.rpow_le_rpow h (by positivity)

theorem moment_root_factor {c N L p : ℝ} (hc : 0 ≤ c) (hN : 0 < N)
    (hL : 0 ≤ L) (E : ℝ) :
    (c*N^E*L)^(1/p) = c^(1/p)*N^(E/p)*L^(1/p) := by
  rw [Real.mul_rpow (mul_nonneg hc (Real.rpow_nonneg hN.le E)) hL,
    Real.mul_rpow hc (Real.rpow_nonneg hN.le E),←Real.rpow_mul hN.le]
  congr 2
  ring_nf

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
