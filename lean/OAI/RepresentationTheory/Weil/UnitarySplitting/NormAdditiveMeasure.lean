import OAI.RepresentationTheory.Weil.UnitarySplitting.MultiplicativeHaar
import OAI.RepresentationTheory.Weil.UnitarySplitting.NormHaar
import OAI.RepresentationTheory.Weil.UnitarySplitting.NormKernelOpen

/-! # Norm Additive Measure -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.NormAdditiveMeasure.Construction

noncomputable section

section

/-! Comparison of the norm pushforward with multiplicative Haar measure
restricted to the norm subgroup. -/

open _root_.MeasureTheory _root_.Topology
open scoped NNReal

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace Fˣ] [BorelSpace Fˣ] [MeasurableSpace Eˣ] [BorelSpace Eˣ]
variable (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
variable (hEmbedding : Continuous (algebraMap F E)) (hQuadratic : Module.finrank F E = 2)
variable (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)

include hF hE hEmbedding hQuadratic hω in
theorem norm_multiplicative_measure_comparison
    (μF : Measure F) [μF.IsAddHaarMeasure] [μF.Regular]
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular] :
    ∃ c : ℝ≥0, 0 < c ∧
      (MultiplicativeHaar.Construction.fieldMultiplicativeMeasure μE).map (Units.map (Algebra.norm F : E →* F)) =
        c • (MultiplicativeHaar.Construction.fieldMultiplicativeMeasure μF).restrict (ω.toMonoidHom.ker : Set Fˣ) := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  let : SecondCountableTopology Fˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : LocallyCompactSpace Fˣ := IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
  let K := ω.toMonoidHom.ker
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  have hopen : IsOpen (K : Set Fˣ) := NormKernelOpen.Construction.quadraticCharacter_kernel_open hQuadratic ω hω
  have hemb : IsOpenEmbedding K.subtype := hopen.isOpenEmbedding_subtypeVal
  let : SecondCountableTopology K := hemb.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace K := hemb.locallyCompactSpace
  let ηF := MultiplicativeHaar.Construction.fieldMultiplicativeMeasure μF
  let ηE := MultiplicativeHaar.Construction.fieldMultiplicativeMeasure μE
  let : ηF.IsHaarMeasure := MultiplicativeHaar.Construction.fieldMultiplicativeMeasure_isHaar hF μF
  let : ηE.IsHaarMeasure := MultiplicativeHaar.Construction.fieldMultiplicativeMeasure_isHaar hE μE
  let ν : Measure K := ηE.map (NormHaar.Construction.normToKernel ω hω)
  let τ : Measure K := ηF.comap K.subtype
  let : ν.IsHaarMeasure := NormHaar.Construction.normToKernel_map_haar hF hEmbedding hQuadratic ω hω ηE
  let : τ.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance) ηF hemb
  let c := Measure.haarScalarFactor ν τ
  have hc : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure ν τ
  have hν : ν = c • τ := Measure.isMulLeftInvariant_eq_smul_of_regular ν τ
  have hh := congrArg (Measure.map K.subtype) hν
  rw [Measure.map_smul _ hemb.continuous.measurable.aemeasurable, DensityPushforward.Construction.map_comap_of_embedding ηF K.subtype hemb.measurableEmbedding] at hh
  change (ηE.map (NormHaar.Construction.normToKernel ω hω)).map K.subtype =
    c • ηF.restrict (Set.range K.subtype) at hh
  rw [Measure.map_map (show Measurable K.subtype from hemb.continuous.measurable)
    (show Measurable (NormHaar.Construction.normToKernel ω hω) from (NormHaar.Construction.normToKernel_continuous hF hEmbedding ω hω).measurable)] at hh
  have hrange : Set.range K.subtype = (K : Set Fˣ) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange] at hh
  exact ⟨c, hc, hh⟩

end

section

/-! The norm pushforward formula for additive Haar measure on the units.
The scaling characters cancel because the field modulus of an element is
the base-field modulus of its quadratic norm. -/

open _root_.MeasureTheory _root_.Topology
open scoped NNReal ENNReal

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace Fˣ] [BorelSpace Fˣ] [MeasurableSpace Eˣ] [BorelSpace Eˣ]
variable [CharZero F]
variable (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
variable (hEmbedding : Continuous (algebraMap F E)) (hQuadratic : Module.finrank F E = 2)
variable (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
variable (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)

include hF hE hEmbedding hQuadratic hne hω in
theorem norm_additive_units_measure_comparison
    (μF : Measure F) [μF.IsAddHaarMeasure] [μF.Regular]
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular] :
    ∃ c : ℝ≥0, 0 < c ∧
      (MultiplicativeHaar.Construction.unitsAdditiveMeasure μE).map (Units.map (Algebra.norm F : E →* F)) =
        c • (MultiplicativeHaar.Construction.unitsAdditiveMeasure μF).restrict (ω.toMonoidHom.ker : Set Fˣ) := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  let N := Units.map (Algebra.norm F : E →* F)
  let w : Fˣ → ℝ≥0∞ := fun a => (FieldModulus.Construction.fieldModulus F a : ℝ≥0∞)
  have hw : Measurable w := measurable_coe_nnreal_ennreal.comp (ModulusMeasure.Construction.fieldModulus_measurable hF)
  have hN : Measurable N := (Units.continuous_map (QuadraticNorm.Construction.fieldNorm_continuous hF hEmbedding)).measurable
  have heq : w ∘ N = fun b : Eˣ => (FieldModulus.Construction.fieldModulus E b : ℝ≥0∞) := by
    funext b
    exact congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞))
      (FieldModulus.Construction.fieldModulus_norm hF hEmbedding hQuadratic σ hne b).symm
  obtain ⟨c, hc, hcomp⟩ := norm_multiplicative_measure_comparison
    hF hE hEmbedding hQuadratic ω hω μF μE
  have hh := congrArg (fun ν : Measure Fˣ => ν.withDensity w) hcomp
  change ((MultiplicativeHaar.Construction.fieldMultiplicativeMeasure μE).map N).withDensity w =
    ((c : ℝ≥0∞) • (MultiplicativeHaar.Construction.fieldMultiplicativeMeasure μF).restrict
      (ω.toMonoidHom.ker : Set Fˣ)).withDensity w at hh
  rw [← DensityPushforward.Construction.map_withDensity_pullback _ N hN w hw, heq,
    MultiplicativeHaar.Construction.fieldMultiplicativeMeasure_withDensity_modulus hE μE,
    withDensity_smul_measure,
    ← restrict_withDensity (NormKernelOpen.Construction.quadraticCharacter_kernel_open hQuadratic ω hω).measurableSet,
    MultiplicativeHaar.Construction.fieldMultiplicativeMeasure_withDensity_modulus hF μF] at hh
  exact ⟨c, hc, hh⟩

end

section

/-! The quadratic field norm sends additive Haar measure to a positive
multiple of additive Haar measure restricted to its set of values. -/

open _root_.MeasureTheory _root_.Topology
open scoped NNReal ENNReal

theorem localField_nullSingleton {F : Type} [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] (hF : ¬ DiscreteTopology F)
    (μ : Measure F) [μ.IsAddHaarMeasure] : NullSingletonClass μ := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · infer_instance

theorem unitsAdditiveMeasure_map_val {F : Type} [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    (hF : ¬ DiscreteTopology F) (μ : Measure F) [μ.IsAddHaarMeasure] :
    (MultiplicativeHaar.Construction.unitsAdditiveMeasure μ).map ((↑) : Fˣ → F) = μ := by
  let : NullSingletonClass μ := localField_nullSingleton hF μ
  rw [MultiplicativeHaar.Construction.unitsAdditiveMeasure, DensityPushforward.Construction.map_comap_of_embedding μ _ MultiplicativeHaar.Construction.unitsVal_measurableEmbedding]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [μ.ae_ne (0 : F)] with x hx
  exact ⟨Units.mk0 x hx, rfl⟩

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
variable [CharZero F]
variable (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
variable (hEmbedding : Continuous (algebraMap F E)) (hQuadratic : Module.finrank F E = 2)
variable (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
variable (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)

include hω in
omit [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E]
  [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E] [CharZero F] in
theorem unitsVal_preimage_norm_range :
    ((↑) : Fˣ → F) ⁻¹' Set.range (Algebra.norm F : E → F) =
      (ω.toMonoidHom.ker : Set Fˣ) := by
  ext a
  change (∃ b : E, Algebra.norm F b = (a : F)) ↔ ω a = 1
  rw [hω]
  constructor
  · rintro ⟨b, hb⟩
    have hbn : b ≠ 0 := Algebra.norm_ne_zero_iff.mp (hb ▸ a.ne_zero)
    exact ⟨Units.mk0 b hbn, hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨(b : E), hb⟩

include hF hE hEmbedding hQuadratic hne hω in
theorem norm_additive_measure_comparison
    (μF : Measure F) [μF.IsAddHaarMeasure] [μF.Regular]
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular] :
    ∃ c : ℝ≥0, 0 < c ∧
      μE.map (Algebra.norm F : E → F) =
        c • μF.restrict (Set.range (Algebra.norm F : E → F)) := by
  let : MeasurableSpace Fˣ := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let : MeasurableSpace Eˣ := borel Eˣ
  let : BorelSpace Eˣ := ⟨rfl⟩
  obtain ⟨c, hc, hh⟩ := norm_additive_units_measure_comparison
    hF hE hEmbedding hQuadratic σ hne ω hω μF μE
  have hNu : Measurable (Units.map (Algebra.norm F : E →* F)) :=
    (Units.continuous_map (QuadraticNorm.Construction.fieldNorm_continuous hF hEmbedding)).measurable
  have hN : Measurable (Algebra.norm F : E → F) :=
    (QuadraticNorm.Construction.fieldNorm_continuous hF hEmbedding).measurable
  have hh' := congrArg (Measure.map ((↑) : Fˣ → F)) hh
  rw [Measure.map_map MultiplicativeHaar.Construction.unitsVal_measurableEmbedding.measurable hNu,
    Measure.map_smul _ MultiplicativeHaar.Construction.unitsVal_measurableEmbedding.measurable.aemeasurable, ← unitsVal_preimage_norm_range ω hω,
    ← MultiplicativeHaar.Construction.unitsVal_measurableEmbedding.restrict_map,
    unitsAdditiveMeasure_map_val hF μF] at hh'
  have heq : ((↑) : Fˣ → F) ∘ Units.map (Algebra.norm F : E →* F) =
      (Algebra.norm F : E → F) ∘ ((↑) : Eˣ → E) := rfl
  rw [heq, ← Measure.map_map hN MultiplicativeHaar.Construction.unitsVal_measurableEmbedding.measurable,
    unitsAdditiveMeasure_map_val hE μE] at hh'
  exact ⟨c, hc, hh'⟩

end

/-! At points sufficiently far from zero, bounded additive translations
preserve the quadratic character and hence membership in the norm image. -/

open _root_.Topology

theorem open_field_character_kernel_ball
    {F : Type} [NormedField F] (ω : Fˣ →ₜ* Circle)
    (hopen : IsOpen (ω.toMonoidHom.ker : Set Fˣ)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ a : Fˣ, ‖(a : F) - 1‖ < ε → ω a = 1 := by
  let S := ((↑) : Fˣ → F) '' (ω.toMonoidHom.ker : Set Fˣ)
  have hS : IsOpen S := IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ hopen
  have h1 : (1 : F) ∈ S := ⟨1, by simp, rfl⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hS 1 h1
  refine ⟨min r 1, lt_min hr zero_lt_one, min_le_right _ _, fun a ha => ?_⟩
  have ham : (a : F) ∈ Metric.ball 1 r := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact ha.trans_le (min_le_left _ _)
  obtain ⟨b, hb, heq⟩ := hsub ham
  have hab : b = a := Units.ext heq
  exact hab ▸ hb

theorem field_character_eq_of_close_units
    {F : Type} [NormedField F] (ω : Fˣ →ₜ* Circle) (ε : ℝ)
    (hε : ∀ a : Fˣ, ‖(a : F) - 1‖ < ε → ω a = 1)
    (a b : Fˣ) (hab : ‖(a : F) - (b : F)‖ < ε * ‖(b : F)‖) : ω a = ω b := by
  have hbn : 0 < ‖(b : F)‖ := norm_pos_iff.mpr b.ne_zero
  have hdiv : ‖((a / b : Fˣ) : F) - 1‖ < ε := by
    simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [← div_eq_mul_inv]
    rw [div_sub_one b.ne_zero, norm_div]
    exact (div_lt_iff₀ hbn).mpr hab
  have hh := hε (a / b) hdiv
  rwa [map_div, div_eq_one] at hh

theorem quadratic_norm_mem_iff_translate_far
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E] [FiniteDimensional F E]
    (hQuadratic : Module.finrank F E = 2) (ω : Fˣ →ₜ* Circle)
    (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω) (t : F) :
    ∃ R : ℝ, 0 < R ∧ ‖t‖ ≤ R ∧ ∀ x : F, R < ‖x‖ →
      (t + x ∈ Set.range (Algebra.norm F : E → F) ↔ x ∈ Set.range (Algebra.norm F : E → F)) := by
  obtain ⟨ε, hεpos, hεone, hε⟩ := open_field_character_kernel_ball ω
    (NormKernelOpen.Construction.quadraticCharacter_kernel_open hQuadratic ω hω)
  let R := max 1 (‖t‖ / ε)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have htR : ‖t‖ ≤ R := calc
    ‖t‖ ≤ ‖t‖ / ε := (le_div_iff₀ hεpos).mpr (mul_le_of_le_one_right (norm_nonneg t) hεone)
    _ ≤ R := le_max_right _ _
  refine ⟨R, hRpos, htR, fun x hx => ?_⟩
  have hxn : x ≠ 0 := norm_pos_iff.mp (hRpos.trans hx)
  have htx : ‖t‖ < ‖x‖ := htR.trans_lt hx
  have htxn : t + x ≠ 0 := by
    intro heq
    have he : t = -x := eq_neg_of_add_eq_zero_left heq
    rw [he, norm_neg] at htx
    exact lt_irrefl _ htx
  have hsmall : ‖t‖ < ε * ‖x‖ := by
    have hh : ‖t‖ / ε < ‖x‖ := (le_max_right _ _).trans_lt hx
    simpa only [mul_comm] using (div_lt_iff₀ hεpos).mp hh
  have hchar := field_character_eq_of_close_units ω ε hε
    (Units.mk0 (t + x) htxn) (Units.mk0 x hxn) (by simpa using hsmall)
  have hrange := unitsVal_preimage_norm_range ω hω
  have hxnorm : x ∈ Set.range (Algebra.norm F : E → F) ↔ ω (Units.mk0 x hxn) = 1 := by
    exact Set.ext_iff.mp hrange (Units.mk0 x hxn)
  have htxnorm : t + x ∈ Set.range (Algebra.norm F : E → F) ↔
      ω (Units.mk0 (t + x) htxn) = 1 := by
    exact Set.ext_iff.mp hrange (Units.mk0 (t + x) htxn)
  rw [htxnorm, hxnorm, hchar]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.NormAdditiveMeasure.Construction
