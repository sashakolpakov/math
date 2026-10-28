import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # Translations -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Translations.CM.Construction

noncomputable section

/-! Actual spatial translations and their L2 Fourier multipliers. -/

open _root_.MeasureTheory FourierTransform
open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def l2Translation (m : E) : Lp ℂ 2 (volume : Measure E) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : E => x + m) (measurePreserving_add_right volume m)

theorem l2Translation_coe (m : E) (u : Lp ℂ 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), l2Translation m u x = u (x + m) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume m)

def schwartzTranslation (m : E) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun x : E => x + m)
    (by fun_prop) (isometry_add_right m).antilipschitzWith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem schwartzTranslation_apply (m : E) (f : 𝓢(E, ℂ)) (x : E) :
    schwartzTranslation m f x = f (x + m) := rfl

theorem l2Translation_schwartz (m : E) (f : 𝓢(E, ℂ)) :
    l2Translation m (f.toLp 2 (volume : Measure E)) =
      (schwartzTranslation m f).toLp 2 (volume : Measure E) := by
  apply Lp.ext
  filter_upwards [l2Translation_coe m (f.toLp 2 (volume : Measure E)),
    (measurePreserving_add_right volume m).quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 (volume : Measure E)),
    (schwartzTranslation m f).coeFn_toLp 2 (volume : Measure E)] with x hx hf ht
  exact hx.trans (hf.trans ht.symm)

def translationPhaseOperator (m x : E) : ℂ →L[ℂ] ℂ :=
  (Real.fourierChar (inner ℝ m x) : ℂ) • ContinuousLinearMap.id ℂ ℂ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem translationPhaseOperator_continuous (m : E) : Continuous (translationPhaseOperator m) := by
  have hφ : Continuous (fun x : E => (Real.fourierChar (inner ℝ m x) : ℂ)) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  exact hφ.smul continuous_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem translationPhaseOperator_norm (m x : E) : ‖translationPhaseOperator m x‖ ≤ 1 := by
  rw [translationPhaseOperator, norm_smul, Circle.norm_coe, one_mul]
  exact ContinuousLinearMap.norm_id_le

def l2TranslationPhase (m : E) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  LpCoefficients.CM.Construction.boundedFieldLp (translationPhaseOperator m) (translationPhaseOperator_continuous m).aestronglyMeasurable
    (Filter.Eventually.of_forall (translationPhaseOperator_norm m))

theorem l2TranslationPhase_coe (m : E) (u : Lp ℂ 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), l2TranslationPhase m u x =
      (Real.fourierChar (inner ℝ m x) : ℂ) * u x :=
  LpCoefficients.CM.Construction.boundedFieldLp_coe _ _ _ u

theorem fourier_schwartzTranslation (m : E) (f : 𝓢(E, ℂ)) (x : E) :
    (𝓕 (schwartzTranslation m f) : 𝓢(E, ℂ)) x =
      (Real.fourierChar (inner ℝ m x) : ℂ) * (𝓕 f : 𝓢(E, ℂ)) x := by
  exact congrArg (fun g : E → ℂ => g x)
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume (innerₗ E) (f : E → ℂ) m)

theorem fourier_l2Translation_schwartz (m : E) (f : 𝓢(E, ℂ)) :
    𝓕 (l2Translation m (f.toLp 2 (volume : Measure E))) =
      l2TranslationPhase m (𝓕 (f.toLp 2 (volume : Measure E))) := by
  rw [l2Translation_schwartz, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (schwartzTranslation m f) : 𝓢(E, ℂ)).coeFn_toLp 2 (volume : Measure E),
    l2TranslationPhase_coe m ((𝓕 f : 𝓢(E, ℂ)).toLp 2 (volume : Measure E)),
    (𝓕 f : 𝓢(E, ℂ)).coeFn_toLp 2 (volume : Measure E)] with x hx hp hf
  rw [hx, hp, hf, fourier_schwartzTranslation]

/-- The Fourier transform of the actual L2 spatial translation is its phase
multiplier, obtained by density of genuine Schwartz functions. -/
theorem fourier_l2Translation (m : E) (u : Lp ℂ 2 (volume : Measure E)) :
    𝓕 (l2Translation m u) = l2TranslationPhase m (𝓕 u) := by
  have hdense := SchwartzMap.denseRange_toLpCLM (E := E) (F := ℂ)
    (μ := (volume : Measure E)) (p := 2) (by norm_num)
  have hclosed : IsClosed {u : Lp ℂ 2 (volume : Measure E) |
      𝓕 (l2Translation m u) = l2TranslationPhase m (𝓕 u)} :=
    isClosed_eq ((Lp.fourierTransformₗᵢ E ℂ).continuous.comp (l2Translation m).continuous)
      ((l2TranslationPhase m).continuous.comp (Lp.fourierTransformₗᵢ E ℂ).continuous)
  exact (closure_minimal (by
    rintro _ ⟨f, rfl⟩
    exact fourier_l2Translation_schwartz m f) hclosed) (hdense u)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Translations.CM.Construction
