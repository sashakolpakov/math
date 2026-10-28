import OAI.Analysis.Fourier.Restriction.Mixed

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem one_lt_toReal_of_one_lt {a : ℝ≥0∞} (ha : 1 < a) (hat : a ≠ ⊤) :
    1 < a.toReal := by
  have H := (ENNReal.toReal_lt_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤) hat).mpr ha
  simpa only [ENNReal.toReal_one] using H

theorem conjugateExponent_pos {a : ℝ≥0∞} (ha : 1 < a) :
    0 < OAI.Analysis.Fourier.Restriction.conjugateExponent a := by
  by_cases hat : a = ⊤
  · simp [OAI.Analysis.Fourier.Restriction.conjugateExponent, hat]
  · have har := one_lt_toReal_of_one_lt ha hat
    simp only [OAI.Analysis.Fourier.Restriction.conjugateExponent, hat, ↓reduceIte]
    exact div_pos (by linarith) (by linarith)

theorem finiteMeasure_embedding_power_nonneg {a : ℝ≥0∞} {s : ℝ}
    (hs : 0 < s) (hsa : ENNReal.ofReal s ≤ a) :
    0 ≤ 1 / s - 1 / a.toReal := by
  by_cases hat : a = ⊤
  · simp only [hat, ENNReal.toReal_top, div_zero, sub_zero]
    positivity
  · have H := ENNReal.toReal_mono hat hsa
    rw [ENNReal.toReal_ofReal hs.le] at H
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hs H)

/-- An actual diagonal estimate yields every strict mixed estimate above its
line, including the `L∞` input endpoint through finite sphere measure. -/
theorem sphericalExtension_mixed_diagonal {n : ℕ} {a : ℝ≥0∞} {s b : ℝ}
    (ha : 1 < a) (hs : 1 < s) (hsb : s < b)
    (hab : OAI.Analysis.Fourier.Restriction.conjugateExponent a * (s - 1) < b) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hdiag : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal s) volume ≤
        C * eLpNorm g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ g : Space n → ℂ, MemLp g a (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal b) volume ≤
        B * eLpNorm g a (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  have hsp : 0 < s := by linarith
  have hbp : 0 < b := by linarith
  by_cases has : a ≤ ENNReal.ofReal s
  · have hat : a ≠ ⊤ := ne_of_lt (has.trans_lt ENNReal.ofReal_lt_top)
    have har := one_lt_toReal_of_one_lt ha hat
    have hars : a.toReal ≤ s := by
      simpa only [ENNReal.toReal_ofReal hsp.le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top has
    have hrange : a.toReal * (s - 1) / (a.toReal - 1) < b := by
      simpa only [OAI.Analysis.Fourier.Restriction.conjugateExponent, hat, ↓reduceIte, div_mul_eq_mul_div] using hab
    refine ⟨mixedExtensionConstant n a.toReal s b C,
      mixedExtensionConstant_ne_top hsp.le hbp hC, ?_⟩
    intro g hg
    have H := sphericalExtension_mixed har hars hbp hrange hdiag
      (g := g) (by simpa only [ENNReal.ofReal_toReal hat] using hg)
    simpa only [ENNReal.ofReal_toReal hat] using H
  · have hsa : ENNReal.ofReal s ≤ a := le_of_lt (lt_of_not_ge has)
    let M := (OAI.Analysis.Fourier.Restriction.sphereMeasure n univ) ^ (1 / s - 1 / a.toReal)
    have hMt : M ≠ ⊤ := ne_of_lt (ENNReal.rpow_lt_top_of_nonneg
      (finiteMeasure_embedding_power_nonneg hsp hsa) (measure_ne_top _ _))
    refine ⟨mixedExtensionConstant n s s b C * M,
      ENNReal.mul_ne_top (mixedExtensionConstant_ne_top hsp.le hbp hC) hMt, ?_⟩
    intro g hg
    have hrange : s * (s - 1) / (s - 1) < b := by
      rwa [mul_div_cancel_right₀ _ (by linarith : s - 1 ≠ 0)]
    have H := sphericalExtension_mixed hs le_rfl hbp hrange hdiag (hg.mono_exponent hsa)
    have Hembed : eLpNorm g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        eLpNorm g a (OAI.Analysis.Fourier.Restriction.sphereMeasure n) * M := by
      simpa only [ENNReal.toReal_ofReal hsp.le] using
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hsa hg.aestronglyMeasurable
    calc
      _ ≤ mixedExtensionConstant n s s b C * eLpNorm g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := H
      _ ≤ mixedExtensionConstant n s s b C * (eLpNorm g a (OAI.Analysis.Fourier.Restriction.sphereMeasure n) * M) := by gcongr
      _ = _ := by ring

end OAI.Analysis.Fourier.Restriction
