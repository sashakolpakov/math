import OAI.RepresentationTheory.Theta.Adelic.FieldMeasures
import OAI.RepresentationTheory.Theta.Adelic.FieldCayleyPhase

/-! # Field Weak Normalization -/

namespace OAI.RepresentationTheory.Theta.Adelic.FieldWeakNormalization

noncomputable section

/-! The corrected weak open-cell normalization transports exactly through
field coordinates; the reference Haar factor is explicit. -/

open _root_.MeasureTheory

open OAI.RepresentationTheory.Theta.Adelic.FieldMeasures OAI.RepresentationTheory.Theta.Adelic.FieldWeylTransport OAI.RepresentationTheory.Theta.Adelic.FieldCayleyPhase

variable {k l : Type} [NormedField k] [NormedField l] [LocallyCompactSpace k] [LocallyCompactSpace l]
variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
variable [SecondCountableTopology k] [SecondCountableTopology l]
variable (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) (N : ℕ) (ψ : AddChar k ℂ)

theorem correctedWeakOpenCellValue_field
    [(Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure l (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ)).IsAddHaarMeasure]
    (hmap : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).map e = Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure l (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ))
    (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (f h : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ) :
    (FieldMeasures.fieldPositionHaarScale e he hi N : ℂ) *
      Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N g)
        (f ∘ (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N).symm) (h ∘ (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N).symm) =
          Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k N ψ g f h := by
  by_cases hg : (g.val - 1).det ≠ 0
  · have hgl := FieldCayleyPhase.field_openCell e N g hg
    have ht := FieldWeylTransport.weakWeylGaussian_field e he hi N ψ
      (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
      (Measure.pi (fun _ : Fin N ⊕ Fin N => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ))
      (Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg)
      (Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase l N (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N g) hgl)
      (FieldCayleyPhase.schrodingerCayleyPhase_field e N g hg) f h
    rw [FieldMeasures.fieldPositionHaar_map, FieldMeasures.fieldPhaseMeasure_map e he hi N _ _ hmap,
      FieldWeylTransport.weakWeylGaussian_smul_position] at ht
    rw [Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue_open l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) _ hgl,
      Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue_open k N ψ g hg, Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCell, Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCell,
      FieldCayleyPhase.openCellScale_field e he hi N g hg]
    rw [mul_left_comm, ht]
  · have hgl : ¬ ((Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N g).val - 1).det ≠ 0 := by
      intro hl
      rw [FieldCayleyPhase.field_openCell_det] at hl
      apply hg
      exact (map_ne_zero e).mp hl
    rw [Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue, dite_eq_right hgl, Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue, dite_eq_right hg, mul_zero]

end

end OAI.RepresentationTheory.Theta.Adelic.FieldWeakNormalization
