import OAI.RepresentationTheory.Theta.Adelic.FieldWeylTransport
import OAI.RepresentationTheory.Weil.Local.FieldFourier

/-! # Field Measures -/

namespace OAI.RepresentationTheory.Theta.Adelic.FieldMeasures

noncomputable section

/-! Exact reference and self-dual product measures under field coordinates. -/

open _root_.MeasureTheory
open scoped NNReal ComplexConjugate

open OAI.RepresentationTheory.Weil.Local.FieldFourier.Construction

variable {k l : Type} [NormedField k] [NormedField l] [LocallyCompactSpace k] [LocallyCompactSpace l]
variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
variable [SecondCountableTopology k] [SecondCountableTopology l]
variable (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) (N : ℕ)

def fieldPositionHaarScale : ℝ≥0 :=
  Measure.addHaarScalarFactor
    ((Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N).map (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N))
    (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure l N)

theorem fieldPositionHaarScale_pos : 0 < fieldPositionHaarScale e he hi N := by
  let p := Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N
  let : ((Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N).map p).IsAddHaarMeasure :=
    p.isAddHaarMeasure_map _
  exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    ((Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N).map p)
    (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure l N)

theorem fieldPositionHaar_map :
    (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N).map (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N) =
      fieldPositionHaarScale e he hi N • Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure l N := by
  let p := Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N
  let : ((Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N).map p).IsAddHaarMeasure :=
    p.isAddHaarMeasure_map _
  exact Measure.isAddLeftInvariant_eq_smul_of_regular _ _

theorem fieldPositionHaar_integral (f : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ) :
    (∫ x, f x ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
      (fieldPositionHaarScale e he hi N : ℂ) *
        ∫ y, f ((Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N).symm y)
          ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure l N := by
  let p := Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N
  have h := integral_map_equiv (μ := Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
    p.toHomeomorph.toMeasurableEquiv (fun y => f (p.symm y))
  change (∫ y, f (p.symm y) ∂(Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N).map p) = _ at h
  rw [fieldPositionHaar_map, integral_smul_nnreal_measure] at h
  have hp (x : Weil.Local.FunctionsMetaplectic.Construction.Position k N) : p.symm (p.toHomeomorph.toMeasurableEquiv x) = x := p.symm_apply_apply x
  simpa only [hp, NNReal.smul_def, Complex.real_smul] using h.symm

omit [LocallyCompactSpace k] [LocallyCompactSpace l] [SecondCountableTopology k] [SecondCountableTopology l] in
theorem fieldPhaseMeasure_map (μ : Measure k) (ν : Measure l) [SigmaFinite ν]
    (hmap : μ.map e = ν) :
    (Measure.pi (fun _ : Fin N ⊕ Fin N => μ)).map (Weil.UnitarySplitting.FieldCoordinates.Construction.coordinateFieldEquiv (Fin N ⊕ Fin N) e he hi) =
      Measure.pi (fun _ : Fin N ⊕ Fin N => ν) := by
  let : SigmaFinite (μ.map e) := hmap.symm ▸ inferInstance
  have h := Measure.pi_map_pi (μ := fun _ : Fin N ⊕ Fin N => μ) (f := fun _ => e)
    (fun _ => he.measurable.aemeasurable)
  simpa only [hmap] using! h

end

end OAI.RepresentationTheory.Theta.Adelic.FieldMeasures
