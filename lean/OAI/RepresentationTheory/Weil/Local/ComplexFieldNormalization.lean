import OAI.RepresentationTheory.Weil.Local.ComplexFieldHaar
import OAI.RepresentationTheory.Weil.Local.ComplexNormalization
import OAI.RepresentationTheory.Weil.Local.FieldFourier

/-! # Complex Field Normalization -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexFieldNormalization.Construction

noncomputable section

/-! The prescribed reference-set Fourier scale for complex topological field presentations. -/

open _root_.MeasureTheory Set _root_.TopologicalSpace
open scoped FourierTransform ComplexConjugate NNReal

theorem complex_compact_character_fourier (K : PositiveCompacts ℂ) (b ξ : ℂ) :
    (∫ y in (K : Set ℂ), ComplexNormalization.Construction.complexCharacter b (-(ξ * y))) =
      𝓕 ((K : Set ℂ).indicator (fun _ => (1 : ℂ))) (conj (b * ξ)) := by
  rw [← ComplexFourierStandard.Construction.scalarFourierIntegral_complex_standard,
    ComplexFourierStandard.Construction.scalarFourierIntegral_indicator _ _ _ K.isCompact.measurableSet]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change ArchimedeanTestSpace.Construction.complexStandardCharacter (b * -(ξ * y)) = ArchimedeanTestSpace.Construction.complexStandardCharacter (-((b * ξ) * y))
    congr 1
    ring

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k]

theorem referenceFourier_complexField
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (b : ℂ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = ComplexNormalization.Construction.complexCharacter b) (ξ : ℂ) :
    FunctionsMetaplectic.Construction.referenceFourier k ψ (e.symm ξ) = (ComplexFieldHaar.Construction.fieldComplexHaarFactor e he he' : ℂ) *
      𝓕 ((ComplexFieldHaar.Construction.complexFieldReferenceCompact e he he' : Set ℂ).indicator
        (fun _ => (1 : ℂ))) (conj (b * ξ)) := by
  have hpre : e ⁻¹' (ComplexFieldHaar.Construction.complexFieldReferenceCompact e he he' : Set ℂ) =
      (FunctionsMetaplectic.Construction.referenceCompact k : Set k) := e.injective.preimage_image _
  rw [FunctionsMetaplectic.Construction.referenceFourier, ← hpre, ComplexFieldHaar.Construction.fieldComplexHaar_setIntegral e he he',
    ← complex_compact_character_fourier]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [← hψ]
    change ψ (-(e.symm ξ * e.symm y)) = ψ (e.symm (-(ξ * y)))
    congr 1
    rw [map_neg, map_mul]

theorem fourierHaarScaleSquared_complexField
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (b : ℂ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = ComplexNormalization.Construction.complexCharacter b) (hb : b ≠ 0) :
    FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ =
      (ComplexFieldHaar.Construction.fieldComplexHaarFactor e he he' : ℝ) ^ 2 / (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ) := by
  let r : ℝ := ComplexFieldHaar.Construction.fieldComplexHaarFactor e he he'
  let K := ComplexFieldHaar.Construction.complexFieldReferenceCompact e he he'
  let f : ℂ → ℂ := (K : Set ℂ).indicator (fun _ => 1)
  have hr : r ≠ 0 := (show 0 < r from ComplexFieldHaar.Construction.fieldComplexHaarFactor_pos e he he').ne'
  have hK : volume.real (K : Set ℂ) ≠ 0 := (ComplexFieldHaar.Construction.complexFieldReferenceCompact_volume_pos e he he').ne'
  have hchange := CharacterScaling.Construction.integral_scalar_field b hb (volume : Measure ℂ) (fun ξ => ‖𝓕 f (conj ξ)‖ ^ 2)
  simp only [smul_eq_mul] at hchange
  have hconj : (∫ ξ : ℂ, ‖𝓕 f (conj ξ)‖ ^ 2) = ∫ ξ : ℂ, ‖𝓕 f ξ‖ ^ 2 := by
    simpa using! Complex.conjLIE.measurePreserving.integral_comp
      Complex.conjLIE.toHomeomorph.measurableEmbedding (fun ξ => ‖𝓕 f ξ‖ ^ 2)
  rw [FunctionsMetaplectic.Construction.fourierHaarScaleSquared, ComplexFieldHaar.Construction.fieldComplexHaar_integral e he he',
    ComplexFieldHaar.Construction.complexFieldReferenceCompact_measure e he he']
  simp_rw [referenceFourier_complexField e he he' ψ b hψ, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (ComplexFieldHaar.Construction.fieldComplexHaarFactor e he he').coe_nonneg, mul_pow]
  rw [integral_const_mul]
  change (r * (r ^ 2 * ∫ ξ, ‖𝓕 f (conj (b * ξ))‖ ^ 2)) / (r * volume.real (K : Set ℂ)) =
    r ^ 2 / (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ)
  rw [hchange, hconj, RealFourierLp.Construction.real_indicator_fourier_norm_sq K.isCompact.measurableSet K.isCompact.measure_ne_top]
  field_simp

theorem fourierHaarScaleSquared_complexField_pos
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (b : ℂ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = ComplexNormalization.Construction.complexCharacter b) (hb : b ≠ 0) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ := by
  rw [fourierHaarScaleSquared_complexField e he he' ψ b hψ hb]
  exact div_pos (sq_pos_of_pos (ComplexFieldHaar.Construction.fieldComplexHaarFactor_pos e he he')) (DeterminantMeasure.Construction.haarModulus_pos ℂ hb)

theorem selfDualMeasure_complexField_map
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (b : ℂ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = ComplexNormalization.Construction.complexCharacter b) (hb : b ≠ 0) :
    (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).map e = FunctionsMetaplectic.Construction.selfDualMeasure ℂ (FieldFourier.Construction.fieldCharacter e ψ) := by
  let r := ComplexFieldHaar.Construction.fieldComplexHaarFactor e he he'
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast (ComplexFieldHaar.Construction.fieldComplexHaarFactor_pos e he he').ne'
  have hs : Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (DeterminantMeasure.Construction.haarModulus_pos ℂ hb)).ne'
  have hscale : (Real.sqrt ((r : ℝ) ^ 2 / (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ)))⁻¹ * r =
      Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ) := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq r.coe_nonneg]
    field_simp
  rw [hψ, ComplexNormalization.Construction.selfDualMeasure_complex b hb, FunctionsMetaplectic.Construction.selfDualMeasure, Measure.map_smul _ he.measurable.aemeasurable,
    fourierHaarScaleSquared_complexField e he he' ψ b hψ hb, ComplexFieldHaar.Construction.fieldComplexHaar_map e he he']
  change ENNReal.ofReal ((Real.sqrt ((r : ℝ) ^ 2 / (DeterminantMeasure.Construction.haarModulus ℂ b : ℝ)))⁻¹) • (r • volume) = _
  rw [ENNReal.smul_def, smul_smul, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity), hscale]

theorem complexField_selfDual_normalization
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ ∧ (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure ∧
      (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).map e = FunctionsMetaplectic.Construction.selfDualMeasure ℂ (FieldFourier.Construction.fieldCharacter e ψ) := by
  have hηc : Continuous (fun t => FieldFourier.Construction.fieldCharacter e ψ t) := hc.comp he'
  have hηu : ∀ t, ‖FieldFourier.Construction.fieldCharacter e ψ t‖ = 1 := fun t => hu (e.symm t)
  have hηn : ∃ t, FieldFourier.Construction.fieldCharacter e ψ t ≠ 1 := by
    obtain ⟨t, ht⟩ := hn
    refine ⟨e t, ?_⟩
    change ψ (e.symm (e t)) ≠ 1
    rwa [e.symm_apply_apply]
  obtain ⟨b, hb, hψ⟩ := ComplexNormalization.Construction.continuous_nontrivial_unitary_complex_character (FieldFourier.Construction.fieldCharacter e ψ) hηc hηu hηn
  have hpos := fourierHaarScaleSquared_complexField_pos e he he' ψ b hψ hb
  exact ⟨hpos, FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ hpos,
    selfDualMeasure_complexField_map e he he' ψ b hψ hb⟩

end

end OAI.RepresentationTheory.Weil.Local.ComplexFieldNormalization.Construction
