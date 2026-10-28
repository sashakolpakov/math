import OAI.RepresentationTheory.Weil.Local.FieldCoordinates
import OAI.RepresentationTheory.Weil.Local.ArchimedeanTestSpace

/-! # Complex Field Haar -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexFieldHaar.Construction

noncomputable section

/-! The complex Lebesgue Haar factor and the transported reference compact set. -/

open _root_.MeasureTheory Set _root_.TopologicalSpace
open scoped NNReal

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k]

def fieldComplexHaarFactor (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm) : ℝ≥0 :=
  FieldCoordinates.Construction.fieldReferenceHaarFactor e he he' * ArchimedeanTestSpace.Construction.complexReferenceHaarFactor

theorem fieldComplexHaarFactor_pos (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm) :
    0 < fieldComplexHaarFactor e he he' :=
  mul_pos (FieldCoordinates.Construction.fieldReferenceHaarFactor_pos e he he') ArchimedeanTestSpace.Construction.complexReferenceHaarFactor_pos

theorem fieldComplexHaar_map (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm) :
    (Measure.addHaar : Measure k).map e = fieldComplexHaarFactor e he he' • volume := by
  rw [FieldCoordinates.Construction.fieldReferenceHaar_map e he he',
    Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℂ) volume, smul_smul]
  rfl

theorem fieldComplexHaar_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm) (f : k → E) :
    (∫ x, f x ∂Measure.addHaar) =
      (fieldComplexHaarFactor e he he' : ℝ) • ∫ y : ℂ, f (e.symm y) := by
  have hi := integral_map_equiv (μ := (Measure.addHaar : Measure k))
    (FieldCoordinates.Construction.fieldAddHomeomorph e he he').toHomeomorph.toMeasurableEquiv (fun y => f (e.symm y))
  change (∫ y, f (e.symm y) ∂(Measure.addHaar : Measure k).map e) =
    ∫ x, f (e.symm (e x)) ∂Measure.addHaar at hi
  rw [fieldComplexHaar_map e he he', integral_smul_nnreal_measure] at hi
  simpa only [RingEquiv.symm_apply_apply, NNReal.smul_def] using hi.symm

def complexFieldReferenceCompact (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm) :
    PositiveCompacts ℂ :=
  (FunctionsMetaplectic.Construction.referenceCompact k).map e he (FieldCoordinates.Construction.fieldAddHomeomorph e he he').toHomeomorph.isOpenMap

omit [MeasurableSpace k] [BorelSpace k] in
theorem complexFieldReferenceCompact_volume_pos (e : k ≃+* ℂ) (he : Continuous e)
    (he' : Continuous e.symm) :
    0 < volume.real (complexFieldReferenceCompact e he he' : Set ℂ) := by
  apply ENNReal.toReal_pos
  · exact (Measure.measure_pos_of_nonempty_interior volume
      (complexFieldReferenceCompact e he he').interior_nonempty).ne'
  · exact (complexFieldReferenceCompact e he he').isCompact.measure_ne_top

theorem complexFieldReferenceCompact_measure (e : k ≃+* ℂ) (he : Continuous e)
    (he' : Continuous e.symm) :
    (Measure.addHaar : Measure k).real (FunctionsMetaplectic.Construction.referenceCompact k : Set k) =
      (fieldComplexHaarFactor e he he' : ℝ) *
        volume.real (complexFieldReferenceCompact e he he' : Set ℂ) := by
  have hm := congrArg (fun μ : Measure ℂ => μ.real (complexFieldReferenceCompact e he he' : Set ℂ))
    (fieldComplexHaar_map e he he')
  rw [map_measureReal_apply he.measurable (complexFieldReferenceCompact e he he').isCompact.measurableSet,
    measureReal_nnreal_smul_apply] at hm
  have hpre : e ⁻¹' (complexFieldReferenceCompact e he he' : Set ℂ) =
      (FunctionsMetaplectic.Construction.referenceCompact k : Set k) := e.injective.preimage_image _
  rwa [hpre] at hm

theorem fieldComplexHaar_setIntegral (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (f : k → ℂ) (s : Set ℂ) :
    (∫ x in e ⁻¹' s, f x ∂Measure.addHaar) =
      (fieldComplexHaarFactor e he he' : ℂ) * ∫ y in s, f (e.symm y) := by
  have hi := setIntegral_map_equiv (μ := (Measure.addHaar : Measure k))
    (FieldCoordinates.Construction.fieldAddHomeomorph e he he').toHomeomorph.toMeasurableEquiv (fun y => f (e.symm y)) s
  change (∫ y in s, f (e.symm y) ∂(Measure.addHaar : Measure k).map e) =
    ∫ x in e ⁻¹' s, f (e.symm (e x)) ∂Measure.addHaar at hi
  rw [fieldComplexHaar_map e he he', Measure.restrict_smul, integral_smul_nnreal_measure] at hi
  simpa only [RingEquiv.symm_apply_apply, NNReal.smul_def, Complex.real_smul] using hi.symm

end

end OAI.RepresentationTheory.Weil.Local.ComplexFieldHaar.Construction
