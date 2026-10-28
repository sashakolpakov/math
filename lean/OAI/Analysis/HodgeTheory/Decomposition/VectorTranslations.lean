import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # Vector Translations -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorTranslations.Constructions

noncomputable section

/-! Actual vector-valued spatial translations and their L² Fourier multipliers. -/

open _root_.MeasureTheory FourierTransform
open scoped SchwartzMap

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def vectorL2Translation (m : E) : Lp F 2 (volume : Measure E) →ₗᵢ[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : E => x + m) (measurePreserving_add_right volume m)

omit [CompleteSpace F] in
theorem vectorL2Translation_coe (m : E) (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), vectorL2Translation m u x = u (x + m) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume m)

def vectorSchwartzTranslation (m : E) : 𝓢(E, F) →L[ℂ] 𝓢(E, F) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun x : E => x + m)
    (by fun_prop) (isometry_add_right m).antilipschitzWith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
theorem vectorSchwartzTranslation_apply (m : E) (f : 𝓢(E, F)) (x : E) :
    vectorSchwartzTranslation m f x = f (x + m) := rfl

omit [CompleteSpace F] in
theorem vectorL2Translation_schwartz (m : E) (f : 𝓢(E, F)) :
    vectorL2Translation m (f.toLp 2 (volume : Measure E)) =
      (vectorSchwartzTranslation m f).toLp 2 (volume : Measure E) := by
  apply Lp.ext
  filter_upwards [vectorL2Translation_coe m (f.toLp 2 (volume : Measure E)),
    (measurePreserving_add_right volume m).quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 (volume : Measure E)),
    (vectorSchwartzTranslation m f).coeFn_toLp 2 (volume : Measure E)] with x hx hf ht
  exact hx.trans (hf.trans ht.symm)

def vectorTranslationPhaseOperator (m x : E) : F →L[ℂ] F :=
  (Real.fourierChar (inner ℝ m x) : ℂ) • ContinuousLinearMap.id ℂ F

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
theorem vectorTranslationPhaseOperator_continuous (m : E) : Continuous (vectorTranslationPhaseOperator (F := F) m) := by
  have hφ : Continuous (fun x : E => (Real.fourierChar (inner ℝ m x) : ℂ)) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  exact hφ.smul continuous_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
theorem vectorTranslationPhaseOperator_norm (m x : E) : ‖vectorTranslationPhaseOperator (F := F) m x‖ ≤ 1 := by
  rw [vectorTranslationPhaseOperator, norm_smul, Circle.norm_coe, one_mul]
  exact ContinuousLinearMap.norm_id_le

def vectorL2TranslationPhase (m : E) : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp (vectorTranslationPhaseOperator m) (vectorTranslationPhaseOperator_continuous m).aestronglyMeasurable
    (Filter.Eventually.of_forall (vectorTranslationPhaseOperator_norm m))

omit [CompleteSpace F] in
theorem vectorL2TranslationPhase_coe (m : E) (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), vectorL2TranslationPhase m u x =
      (Real.fourierChar (inner ℝ m x) : ℂ) • u x :=
  AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp_coe _ _ _ u

omit [CompleteSpace F] in
theorem fourier_vectorSchwartzTranslation (m : E) (f : 𝓢(E, F)) (x : E) :
    (𝓕 (vectorSchwartzTranslation m f) : 𝓢(E, F)) x =
      (Real.fourierChar (inner ℝ m x) : ℂ) • (𝓕 f : 𝓢(E, F)) x := by
  exact congrArg (fun g : E → F => g x)
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume (innerₗ E) (f : E → F) m)

theorem fourier_vectorL2Translation_schwartz (m : E) (f : 𝓢(E, F)) :
    𝓕 (vectorL2Translation m (f.toLp 2 (volume : Measure E))) =
      vectorL2TranslationPhase m (𝓕 (f.toLp 2 (volume : Measure E))) := by
  rw [vectorL2Translation_schwartz, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (vectorSchwartzTranslation m f) : 𝓢(E, F)).coeFn_toLp 2 (volume : Measure E),
    vectorL2TranslationPhase_coe m ((𝓕 f : 𝓢(E, F)).toLp 2 (volume : Measure E)),
    (𝓕 f : 𝓢(E, F)).coeFn_toLp 2 (volume : Measure E)] with x hx hp hf
  rw [hx, hp, hf, fourier_vectorSchwartzTranslation]

/-- The Fourier transform of the actual L2 spatial translation is its phase
multiplier, obtained by density of genuine Schwartz functions. -/
theorem fourier_vectorL2Translation (m : E) (u : Lp F 2 (volume : Measure E)) :
    𝓕 (vectorL2Translation m u) = vectorL2TranslationPhase m (𝓕 u) := by
  have hdense := SchwartzMap.denseRange_toLpCLM (E := E) (F := F)
    (μ := (volume : Measure E)) (p := 2) (by norm_num)
  have hclosed : IsClosed {u : Lp F 2 (volume : Measure E) |
      𝓕 (vectorL2Translation m u) = vectorL2TranslationPhase m (𝓕 u)} :=
    isClosed_eq ((Lp.fourierTransformₗᵢ E F).continuous.comp (vectorL2Translation m).continuous)
      ((vectorL2TranslationPhase m).continuous.comp (Lp.fourierTransformₗᵢ E F).continuous)
  exact (closure_minimal (by
    rintro _ ⟨f, rfl⟩
    exact fourier_vectorL2Translation_schwartz m f) hclosed) (hdense u)

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorTranslations.Constructions
