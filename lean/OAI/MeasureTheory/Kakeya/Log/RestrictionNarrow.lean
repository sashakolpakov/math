import OAI.MeasureTheory.Kakeya.Log.RestrictionDuality
import OAI.MeasureTheory.Kakeya.Log.SmoothingWeight
import OAI.Analysis.Fourier.Restriction.CriticalInput

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem restrictionInputExponent_conjugate {n : ℕ} (hn : 2 ≤ n) :
    OAI.Analysis.Fourier.Restriction.restrictionInputExponent n / (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n - 1) = OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (n : ℝ) + 1 ≠ 0 := by positivity
  have hnm : (n : ℝ) - 1 ≠ 0 := by linarith
  apply (div_eq_iff (show OAI.Analysis.Fourier.Restriction.restrictionInputExponent n - 1 ≠ 0 by
    linarith [(OAI.Analysis.Fourier.Restriction.restrictionInputExponent_bounds hn).1])).mpr
  unfold OAI.Analysis.Fourier.Restriction.restrictionInputExponent OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  field_simp [hnp, hnm]
  ring

/-- The narrow annular convolution bound at the critical restriction input
exponent. Duality and compact approximation do not increase the logarithmic
degree or introduce dependence on the support radius. -/
theorem logarithmic_narrow_compact_convolution (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {φ : ℝ → ℝ} (hφc : ContDiff ℝ ∞ φ)
    (hφ : tsupport φ ⊆ Icc (-(1 / 4)) (1 / 4))
    (heven : ∀ t, φ (-t) = φ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ f : Space n → ℂ,
      Integrable f → MemLp f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume →
      ∀ R : ℝ, 0 ≤ R → (∀ x, R < ‖x‖ → f x = 0) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalKernelConvolution (narrowKernel n φ T) f)
        (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume ≤
        ENNReal.ofReal (C * (1 + Real.log T) ^ (2 * n + 5)) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume := by
  obtain ⟨C, hC, hbound⟩ := logarithmic_narrow_multiplier hlog hn hφc hφ heven
  refine ⟨C, hC, ?_⟩
  intro T hT f hf hfp R hR hfs
  apply even_multiplier_compact_convolution_bound
    (narrowSymbol_contDiff hφc hφ hT) (narrowSymbol_hasCompactSupport hφ hT)
    (fun ξ ↦ by simp only [narrowSymbol, norm_neg])
    (OAI.Analysis.Fourier.Restriction.restrictionInputExponent_bounds hn).1 ENNReal.ofReal_ne_top
    (fun g ↦ ?_) hf hfp hR hfs
  rw [restrictionInputExponent_conjugate hn]
  exact hbound T hT g

end OAI.MeasureTheory.Kakeya
