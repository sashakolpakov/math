import OAI.Analysis.Fourier.Cone.InterpolationMixed

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Cone.FiniteExtension

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} [IsFiniteMeasure μ] {ν : Measure Y} {T : FiniteExtension μ ν}

theorem mixed_diagonal {a : ℝ≥0∞} {s b : ℝ}
    (ha : 1 < a) (hs : 1 < s) (hsb : s < b)
    (hab : OAI.Analysis.Fourier.Restriction.conjugateExponent a * (s - 1) < b) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hdiag : ∀ g : X → ℂ, MemLp g (ENNReal.ofReal s) μ →
      eLpNorm (T g) (ENNReal.ofReal s) ν ≤
        C * eLpNorm g (ENNReal.ofReal s) μ) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ g : X → ℂ, MemLp g a μ →
      eLpNorm (T g) (ENNReal.ofReal b) ν ≤
        B * eLpNorm g a μ := by
  have hsp : 0 < s := by linarith
  have hbp : 0 < b := by linarith
  by_cases has : a ≤ ENNReal.ofReal s
  · have hat : a ≠ ⊤ := ne_of_lt (has.trans_lt ENNReal.ofReal_lt_top)
    have har := OAI.Analysis.Fourier.Restriction.one_lt_toReal_of_one_lt ha hat
    have hars : a.toReal ≤ s := by
      simpa only [ENNReal.toReal_ofReal hsp.le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top has
    have hrange : a.toReal * (s - 1) / (a.toReal - 1) < b := by
      simpa only [OAI.Analysis.Fourier.Restriction.conjugateExponent, hat, ↓reduceIte, div_mul_eq_mul_div] using hab
    refine ⟨FiniteExtension.mixedExtensionConstant μ a.toReal s b C,
      FiniteExtension.mixedExtensionConstant_ne_top hsp.le hbp hC, ?_⟩
    intro g hg
    have H := FiniteExtension.mixed har hars hbp hrange hdiag
      (g := g) (by simpa only [ENNReal.ofReal_toReal hat] using hg)
    simpa only [ENNReal.ofReal_toReal hat] using H
  · have hsa : ENNReal.ofReal s ≤ a := le_of_lt (lt_of_not_ge has)
    let M := (μ univ) ^ (1 / s - 1 / a.toReal)
    have hMt : M ≠ ⊤ := ne_of_lt (ENNReal.rpow_lt_top_of_nonneg
      (OAI.Analysis.Fourier.Restriction.finiteMeasure_embedding_power_nonneg hsp hsa) (measure_ne_top _ _))
    refine ⟨FiniteExtension.mixedExtensionConstant μ s s b C * M,
      ENNReal.mul_ne_top (FiniteExtension.mixedExtensionConstant_ne_top hsp.le hbp hC) hMt, ?_⟩
    intro g hg
    have hrange : s * (s - 1) / (s - 1) < b := by
      rwa [mul_div_cancel_right₀ _ (by linarith : s - 1 ≠ 0)]
    have H := FiniteExtension.mixed hs le_rfl hbp hrange hdiag (hg.mono_exponent hsa)
    have Hembed : eLpNorm g (ENNReal.ofReal s) μ ≤
        eLpNorm g a μ * M := by
      simpa only [ENNReal.toReal_ofReal hsp.le] using
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hsa hg.aestronglyMeasurable
    calc
      _ ≤ FiniteExtension.mixedExtensionConstant μ s s b C * eLpNorm g (ENNReal.ofReal s) μ := H
      _ ≤ FiniteExtension.mixedExtensionConstant μ s s b C * (eLpNorm g a μ * M) := by gcongr
      _ = _ := by ring

end OAI.Analysis.Fourier.Cone.FiniteExtension
