import OAI.RepresentationTheory.Weil.Local.FieldCoordinates
import OAI.RepresentationTheory.Weil.Local.FieldFourier
import OAI.RepresentationTheory.Weil.Local.ArchimedeanNorm
import OAI.RepresentationTheory.Weil.Local.RealPower

/-! # Real Field Eq -/

namespace OAI.RepresentationTheory.Weil.Local.RealFieldEq.Construction

noncomputable section

section

/-! Actual Gaussian limits and phases in every real topological field presentation. -/

open _root_.MeasureTheory Filter
open scoped NNReal _root_.Topology

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k]

def fieldRealHaarFactor (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm) : ℝ≥0 :=
  FieldCoordinates.Construction.fieldReferenceHaarFactor e he he' * Gaussian.Construction.realReferenceHaarFactor

theorem fieldRealHaarFactor_pos (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm) :
    0 < fieldRealHaarFactor e he he' :=
  mul_pos (FieldCoordinates.Construction.fieldReferenceHaarFactor_pos e he he') Gaussian.Construction.realReferenceHaarFactor_pos

theorem fieldRealHaar_integral (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (f : k → ℂ) :
    (∫ x, f x ∂Measure.addHaar) =
      (fieldRealHaarFactor e he he' : ℂ) * ∫ y : ℝ, f (e.symm y) := by
  rw [FieldCoordinates.Construction.fieldReferenceHaar_integral e he he' f,
    Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℝ) volume,
    integral_smul_nnreal_measure]
  simp only [fieldRealHaarFactor, Gaussian.Construction.realReferenceHaarFactor, NNReal.coe_mul, Complex.ofReal_mul,
    NNReal.smul_def, Complex.real_smul, mul_assoc]

omit [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] in
theorem fieldCharacter_real_apply (e : k ≃+* ℝ) (ψ : AddChar k ℂ) (c : ℝ)
    (hψ : FieldFourier.Construction.fieldCharacter e ψ = Gaussian.Construction.realCharacter c) (t : k) :
    ψ t = Gaussian.Construction.realCharacter c (e t) := by
  have hh := congrArg (fun η : AddChar ℝ ℂ => η (e t)) hψ
  change ψ (e.symm (e t)) = _ at hh
  simpa only [RingEquiv.symm_apply_apply] using hh

theorem regularizedGaussian_realField_power
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (c s : ℝ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = Gaussian.Construction.realCharacter c)
    (hNorm : ∀ x : ℝ, ‖e.symm x‖ = |x| ^ s) (a : k) (ε : ℝ) :
    FunctionsMetaplectic.Construction.regularizedGaussian k ψ a ε =
      (fieldRealHaarFactor e he he' : ℂ) *
        ∫ x, RealPower.Construction.realPowerDamping (s * 2) ε (c * e a) x := by
  rw [FunctionsMetaplectic.Construction.regularizedGaussian, fieldRealHaar_integral e he he']
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    have hn : (|x| ^ s) ^ (2 : ℕ) = |x| ^ (s * 2) := by
      rw [Real.rpow_mul (abs_nonneg x), Real.rpow_two]
    rw [hNorm x, hn, RealPower.Construction.realPowerDamping, fieldCharacter_real_apply e ψ c hψ]
    congr 1
    rw [map_div₀, map_mul, map_pow, RingEquiv.apply_symm_apply, map_ofNat,
      Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply]
    congr 1
    push_cast
    ring

theorem regularizedGaussian_realField_tendsto
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (c s : ℝ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = Gaussian.Construction.realCharacter c)
    (hNorm : ∀ x : ℝ, ‖e.symm x‖ = |x| ^ s) (hs : 0 < s) (hc : c ≠ 0)
    (a : k) (ha : a ≠ 0) :
    Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ))
      (𝓝 ((fieldRealHaarFactor e he he' : ℂ) *
        (Complex.I / ((c : ℂ) * e a)) ^ (1 / 2 : ℂ))) := by
  have ht := (RealPower.Construction.realPowerDamping_integral_tendsto (s * 2) (c * e a)
    (mul_pos hs (by norm_num)) (mul_ne_zero hc ((map_ne_zero e).mpr ha))).const_mul
      (fieldRealHaarFactor e he he' : ℂ)
  simp only [Complex.ofReal_mul] at ht
  apply ht.congr
  intro ε
  exact (regularizedGaussian_realField_power e he he' ψ c s hψ hNorm a ε).symm

theorem gaussianIntegral_realField_eq
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (c s : ℝ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = Gaussian.Construction.realCharacter c)
    (hNorm : ∀ x : ℝ, ‖e.symm x‖ = |x| ^ s) (hs : 0 < s) (hc : c ≠ 0)
    (a : k) (ha : a ≠ 0) :
    FunctionsMetaplectic.Construction.gaussianIntegral k ψ a = (fieldRealHaarFactor e he he' : ℂ) *
      (Complex.I / ((c : ℂ) * e a)) ^ (1 / 2 : ℂ) :=
  (regularizedGaussian_realField_tendsto e he he' ψ c s hψ hNorm hs hc a ha).limUnder_eq

theorem gaussianIntegral_realField_ne_zero
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (c s : ℝ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = Gaussian.Construction.realCharacter c)
    (hNorm : ∀ x : ℝ, ‖e.symm x‖ = |x| ^ s) (hs : 0 < s) (hc : c ≠ 0)
    (a : k) (ha : a ≠ 0) : FunctionsMetaplectic.Construction.gaussianIntegral k ψ a ≠ 0 := by
  rw [gaussianIntegral_realField_eq e he he' ψ c s hψ hNorm hs hc a ha]
  apply mul_ne_zero
  · exact_mod_cast (fieldRealHaarFactor_pos e he he').ne'
  · apply Complex.cpow_ne_zero_iff.mpr
    exact Or.inl (div_ne_zero Complex.I_ne_zero (mul_ne_zero
      (Complex.ofReal_ne_zero.mpr hc) (Complex.ofReal_ne_zero.mpr ((map_ne_zero e).mpr ha))))

theorem gaussianIndex_realField_eq
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (c s : ℝ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = Gaussian.Construction.realCharacter c)
    (hNorm : ∀ x : ℝ, ‖e.symm x‖ = |x| ^ s) (hs : 0 < s) (hc : c ≠ 0)
    (a : k) (ha : a ≠ 0) :
    FunctionsMetaplectic.Construction.gaussianIndex k ψ a = FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (e a) := by
  rw [Gaussian.Construction.gaussianIndex_real_eq c (e a) hc ((map_ne_zero e).mpr ha), FunctionsMetaplectic.Construction.gaussianIndex,
    gaussianIntegral_realField_eq e he he' ψ c s hψ hNorm hs hc a ha]
  exact Gaussian.Construction.phase_positive_mul _ (fieldRealHaarFactor_pos e he he') _

theorem realField_gaussian_normalization [CompleteSpace k] [CharZero k]
    (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1)
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) :
    ∀ a : k, a ≠ 0 →
      (Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) ∧
        FunctionsMetaplectic.Construction.gaussianIntegral k ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex k ψ a ^ 8 = 1) ∧
      FunctionsMetaplectic.Construction.gaussianIndex k ψ a = FunctionsMetaplectic.Construction.gaussianIndex ℝ (FieldFourier.Construction.fieldCharacter e ψ) (e a) := by
  obtain ⟨s, hs, _, hNorm⟩ := ArchimedeanNorm.Construction.continuous_real_embedding_norm_power hArch e.symm.toRingHom he'
  have hηc : Continuous (fun t => FieldFourier.Construction.fieldCharacter e ψ t) := hc.comp he'
  have hηu : ∀ t, ‖FieldFourier.Construction.fieldCharacter e ψ t‖ = 1 := fun t => hu (e.symm t)
  have hηn : ∃ t, FieldFourier.Construction.fieldCharacter e ψ t ≠ 1 := by
    obtain ⟨t, ht⟩ := hn
    refine ⟨e t, ?_⟩
    change ψ (e.symm (e t)) ≠ 1
    rwa [e.symm_apply_apply]
  obtain ⟨c, hcz, hψ⟩ := RealCharacters.Construction.continuous_nontrivial_unitary_real_character (FieldFourier.Construction.fieldCharacter e ψ) hηc hηu hηn
  intro a ha
  have hγ := gaussianIndex_realField_eq e he he' ψ c s hψ hNorm hs hcz a ha
  refine ⟨⟨?_, gaussianIntegral_realField_ne_zero e he he' ψ c s hψ hNorm hs hcz a ha, ?_⟩, ?_⟩
  · rw [gaussianIntegral_realField_eq e he he' ψ c s hψ hNorm hs hcz a ha]
    exact regularizedGaussian_realField_tendsto e he he' ψ c s hψ hNorm hs hcz a ha
  · rw [hγ]
    exact Gaussian.Construction.gaussianIndex_real_eighth_power c (e a) hcz ((map_ne_zero e).mpr ha)
  · rwa [hψ]

end

section

/-! Transport of the reference compact set and the Lebesgue Haar factor at a real place. -/

open _root_.MeasureTheory Set _root_.TopologicalSpace
open scoped NNReal

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k]

theorem fieldRealHaar_map (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm) :
    (Measure.addHaar : Measure k).map e = fieldRealHaarFactor e he he' • volume := by
  rw [FieldCoordinates.Construction.fieldReferenceHaar_map e he he',
    Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℝ) volume,
    smul_smul]
  rfl

theorem fieldRealHaar_integral_real (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (f : k → ℝ) :
    (∫ x, f x ∂Measure.addHaar) =
      (fieldRealHaarFactor e he he' : ℝ) * ∫ y : ℝ, f (e.symm y) := by
  have hi := integral_map_equiv (μ := (Measure.addHaar : Measure k))
    (FieldCoordinates.Construction.fieldAddHomeomorph e he he').toHomeomorph.toMeasurableEquiv (fun y => f (e.symm y))
  change (∫ y, f (e.symm y) ∂(Measure.addHaar : Measure k).map e) =
    ∫ x, f (e.symm (e x)) ∂Measure.addHaar at hi
  rw [fieldRealHaar_map e he he', integral_smul_nnreal_measure] at hi
  simpa only [RingEquiv.symm_apply_apply, NNReal.smul_def, smul_eq_mul] using hi.symm

def realFieldReferenceCompact (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm) :
    PositiveCompacts ℝ :=
  (FunctionsMetaplectic.Construction.referenceCompact k).map e he (FieldCoordinates.Construction.fieldAddHomeomorph e he he').toHomeomorph.isOpenMap

omit [MeasurableSpace k] [BorelSpace k] in
theorem realFieldReferenceCompact_mem (e : k ≃+* ℝ) (he : Continuous e)
    (he' : Continuous e.symm) (y : ℝ) :
    y ∈ (realFieldReferenceCompact e he he' : Set ℝ) ↔
      e.symm y ∈ (FunctionsMetaplectic.Construction.referenceCompact k : Set k) := by
  change y ∈ e '' (FunctionsMetaplectic.Construction.referenceCompact k : Set k) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [RingEquiv.symm_apply_apply] using hx
  · intro hy
    exact ⟨e.symm y, hy, e.apply_symm_apply y⟩

omit [MeasurableSpace k] [BorelSpace k] in
theorem realFieldReferenceCompact_volume_pos (e : k ≃+* ℝ) (he : Continuous e)
    (he' : Continuous e.symm) :
    0 < volume.real (realFieldReferenceCompact e he he' : Set ℝ) := by
  apply ENNReal.toReal_pos
  · exact (Measure.measure_pos_of_nonempty_interior volume
      (realFieldReferenceCompact e he he').interior_nonempty).ne'
  · exact (realFieldReferenceCompact e he he').isCompact.measure_ne_top

theorem realFieldReferenceCompact_measure (e : k ≃+* ℝ) (he : Continuous e)
    (he' : Continuous e.symm) :
    (Measure.addHaar : Measure k).real (FunctionsMetaplectic.Construction.referenceCompact k : Set k) =
      (fieldRealHaarFactor e he he' : ℝ) *
        volume.real (realFieldReferenceCompact e he he' : Set ℝ) := by
  have hm := congrArg (fun μ : Measure ℝ => μ.real (realFieldReferenceCompact e he he' : Set ℝ))
    (fieldRealHaar_map e he he')
  rw [map_measureReal_apply he.measurable (realFieldReferenceCompact e he he').isCompact.measurableSet,
    measureReal_nnreal_smul_apply] at hm
  have hpre : e ⁻¹' (realFieldReferenceCompact e he he' : Set ℝ) =
      (FunctionsMetaplectic.Construction.referenceCompact k : Set k) := e.injective.preimage_image _
  rwa [hpre] at hm

theorem fieldRealHaar_setIntegral (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (f : k → ℂ) (s : Set ℝ) :
    (∫ x in e ⁻¹' s, f x ∂Measure.addHaar) =
      (fieldRealHaarFactor e he he' : ℂ) * ∫ y in s, f (e.symm y) := by
  have hi := setIntegral_map_equiv (μ := (Measure.addHaar : Measure k))
    (FieldCoordinates.Construction.fieldAddHomeomorph e he he').toHomeomorph.toMeasurableEquiv (fun y => f (e.symm y)) s
  change (∫ y in s, f (e.symm y) ∂(Measure.addHaar : Measure k).map e) =
    ∫ x in e ⁻¹' s, f (e.symm (e x)) ∂Measure.addHaar at hi
  rw [fieldRealHaar_map e he he', Measure.restrict_smul, integral_smul_nnreal_measure] at hi
  simpa only [RingEquiv.symm_apply_apply, NNReal.smul_def, Complex.real_smul] using hi.symm

end

/-! The prescribed reference-compact normalization for a real topological field. -/

open _root_.MeasureTheory Set _root_.TopologicalSpace
open scoped FourierTransform NNReal

theorem real_compact_character_fourier (K : PositiveCompacts ℝ) (c ξ : ℝ) :
    (∫ y in (K : Set ℝ), Gaussian.Construction.realCharacter c (-(ξ * y))) =
      𝓕 ((K : Set ℝ).indicator (fun _ : ℝ => (1 : ℂ))) (c * ξ) := by
  rw [Real.fourier_eq, ← integral_indicator K.isCompact.measurableSet]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    by_cases hy : y ∈ (K : Set ℝ)
    · simp [hy, Gaussian.Construction.realCharacter, Circle.smul_def, mul_assoc]
      rfl
    · simp [hy]

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k]

theorem referenceFourier_realField
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (c : ℝ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = Gaussian.Construction.realCharacter c) (ξ : ℝ) :
    FunctionsMetaplectic.Construction.referenceFourier k ψ (e.symm ξ) = (fieldRealHaarFactor e he he' : ℂ) *
      𝓕 ((realFieldReferenceCompact e he he' : Set ℝ).indicator
        (fun _ : ℝ => (1 : ℂ))) (c * ξ) := by
  have hpre : e ⁻¹' (realFieldReferenceCompact e he he' : Set ℝ) =
      (FunctionsMetaplectic.Construction.referenceCompact k : Set k) := e.injective.preimage_image _
  rw [FunctionsMetaplectic.Construction.referenceFourier, ← hpre, fieldRealHaar_setIntegral e he he',
    ← real_compact_character_fourier]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [fieldCharacter_real_apply e ψ c hψ, map_neg, map_mul,
      RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem fourierHaarScaleSquared_realField
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (c : ℝ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = Gaussian.Construction.realCharacter c) :
    FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ = (fieldRealHaarFactor e he he' : ℝ) ^ 2 / |c| := by
  let r : ℝ := fieldRealHaarFactor e he he'
  let K := realFieldReferenceCompact e he he'
  let f : ℝ → ℂ := (K : Set ℝ).indicator (fun _ : ℝ => 1)
  have hr : r ≠ 0 := (show 0 < r from fieldRealHaarFactor_pos e he he').ne'
  have hK : volume.real (K : Set ℝ) ≠ 0 := (realFieldReferenceCompact_volume_pos e he he').ne'
  have hchange := Measure.integral_comp_smul (volume : Measure ℝ) (fun ξ => ‖𝓕 f ξ‖ ^ 2) c
  simp only [smul_eq_mul, Module.finrank_self, pow_one, abs_inv] at hchange
  rw [FunctionsMetaplectic.Construction.fourierHaarScaleSquared, fieldRealHaar_integral_real e he he',
    realFieldReferenceCompact_measure e he he']
  simp_rw [referenceFourier_realField e he he' ψ c hψ, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (fieldRealHaarFactor e he he').coe_nonneg, mul_pow]
  rw [integral_const_mul]
  change (r * (r ^ 2 * ∫ ξ, ‖𝓕 f (c * ξ)‖ ^ 2)) / (r * volume.real (K : Set ℝ)) = r ^ 2 / |c|
  rw [hchange, RealFourierLp.Construction.real_indicator_fourier_norm_sq K.isCompact.measurableSet K.isCompact.measure_ne_top]
  field_simp

theorem fourierHaarScaleSquared_realField_pos
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (c : ℝ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = Gaussian.Construction.realCharacter c) (hc : c ≠ 0) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ := by
  rw [fourierHaarScaleSquared_realField e he he' ψ c hψ]
  exact div_pos (sq_pos_of_pos (fieldRealHaarFactor_pos e he he')) (abs_pos.mpr hc)

theorem selfDualMeasure_realField_map
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (c : ℝ) (hψ : FieldFourier.Construction.fieldCharacter e ψ = Gaussian.Construction.realCharacter c) (hc : c ≠ 0) :
    (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).map e = FunctionsMetaplectic.Construction.selfDualMeasure ℝ (FieldFourier.Construction.fieldCharacter e ψ) := by
  let r := fieldRealHaarFactor e he he'
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast (fieldRealHaarFactor_pos e he he').ne'
  have hs : Real.sqrt |c| ≠ 0 := (Real.sqrt_pos.mpr (abs_pos.mpr hc)).ne'
  have hscale : (Real.sqrt ((r : ℝ) ^ 2 / |c|))⁻¹ * r = Real.sqrt |c| := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq r.coe_nonneg]
    field_simp
  rw [hψ, RealFourierLp.Construction.selfDualMeasure_real c hc, FunctionsMetaplectic.Construction.selfDualMeasure, Measure.map_smul _ he.measurable.aemeasurable,
    fourierHaarScaleSquared_realField e he he' ψ c hψ, fieldRealHaar_map e he he']
  change ENNReal.ofReal ((Real.sqrt ((r : ℝ) ^ 2 / |c|))⁻¹) • (r • volume) = _
  rw [ENNReal.smul_def, smul_smul, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity), hscale]

theorem realField_selfDual_normalization
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ ∧ (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure ∧
      (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).map e = FunctionsMetaplectic.Construction.selfDualMeasure ℝ (FieldFourier.Construction.fieldCharacter e ψ) := by
  have hηc : Continuous (fun t => FieldFourier.Construction.fieldCharacter e ψ t) := hc.comp he'
  have hηu : ∀ t, ‖FieldFourier.Construction.fieldCharacter e ψ t‖ = 1 := fun t => hu (e.symm t)
  have hηn : ∃ t, FieldFourier.Construction.fieldCharacter e ψ t ≠ 1 := by
    obtain ⟨t, ht⟩ := hn
    refine ⟨e t, ?_⟩
    change ψ (e.symm (e t)) ≠ 1
    rwa [e.symm_apply_apply]
  obtain ⟨c, hcz, hψ⟩ := RealCharacters.Construction.continuous_nontrivial_unitary_real_character (FieldFourier.Construction.fieldCharacter e ψ) hηc hηu hηn
  have hpos := fourierHaarScaleSquared_realField_pos e he he' ψ c hψ hcz
  exact ⟨hpos, FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ hpos,
    selfDualMeasure_realField_map e he he' ψ c hψ hcz⟩

end

end OAI.RepresentationTheory.Weil.Local.RealFieldEq.Construction
