import OAI.MeasureTheory.Kakeya.Log.RestrictionKernels
import OAI.MeasureTheory.Kakeya.Log.RestrictionNarrow
import OAI.MeasureTheory.Kakeya.Log.KernelAsymptotic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- The logarithmic local-smoothing refinement gives a local critical
spherical restriction estimate with the same logarithmic degree. -/
theorem logarithmic_local_restriction (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ f : Space n → ℂ,
      Measurable f → Integrable f →
      MemLp f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume →
      (∀ y, R < ‖y‖ → f y = 0) →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal ((1 + Real.log R) ^ (2 * n + 5)) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume := by
  obtain ⟨A, B, C, hC, hAB, hAs⟩ := kakeya_narrowKernel_asymptotic (n := n) (by omega : 1 ≤ n)
  obtain ⟨L, hL, hbound⟩ := logarithmic_narrow_compact_convolution hlog hn
    kakeyaLogBump.contDiff kakeyaLogBump_narrow_support (fun t ↦ kakeyaLogBump.neg t)
  let W : ℝ := ((2 * Real.pi) ^ n)⁻¹ * ∫ u, kakeyaLogBump u
  have hW : 0 < W := mul_pos (by positivity) kakeyaLogBump_mass_pos
  apply logarithmic_local_restriction_of_windowed_kernels hn
    (narrowKernel n (kakeyaLogBump : ℝ → ℝ)) (kakeyaLogWeight n)
    hC hW.le hW.le (show 0 < W / 2 by positivity) hL.le hAB
  · intro T hT
    have hT1 : 1 ≤ T := by linarith
    have hm := (narrowSymbol_contDiff (n := n)
      kakeyaLogBump.contDiff kakeyaLogBump_narrow_support hT1).continuous
    exact (OAI.Analysis.Fourier.BochnerRiesz.continuous_angularInverse (hm.integrable_of_hasCompactSupport
      (narrowSymbol_hasCompactSupport kakeyaLogBump_narrow_support hT1))).measurable
  · intro T hT
    have hT1 : 1 ≤ T := by linarith
    obtain ⟨D, _, _, hD⟩ := OAI.Analysis.Fourier.BochnerRiesz.angularInverse_kernel_decay
      (narrowSymbol_contDiff (n := n) kakeyaLogBump.contDiff kakeyaLogBump_narrow_support hT1)
      (narrowSymbol_hasCompactSupport kakeyaLogBump_narrow_support hT1) 0
    refine ⟨D, fun x ↦ ?_⟩
    simpa only [narrowKernel, neg_zero, Real.rpow_zero, mul_one] using (hD x).1
  · intro T _ r
    exact abs_kakeyaLogWeight_le n T r
  · intro T hT r t
    have H := kakeyaLogWeight_lipschitz n (by linarith : 0 < T) r t
    simpa only [W, div_mul_eq_mul_div] using H
  · intro T hT t ht
    apply kakeyaLogWeight_lower n (by linarith)
    rw [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)]
    exact ht.2
  · intro T hT x hx
    exact hAs T (by linarith) x (by linarith)
  · intro T hT f _ hf hfp R hR hfs
    exact hbound T (by linarith) f hf hfp R hR hfs

end OAI.MeasureTheory.Kakeya
