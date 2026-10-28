import OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedCoefficientLabel
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicPeriodHodge
import OAI.AlgebraicGeometry.PELModuli.CMPoints.TypeTransport
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ClosedCoefficientPeriods

/-! # Intrinsic Label Realization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicLabelRealization

noncomputable section

/-! A fixed rational label on the actual marked lattice realizes its
coefficient Hodge structure on the same abelian variety's canonical H1. -/

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {s n : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin n) A) (i : RationalCoefficientLabels.RationalCoefficientLabel P n)

def nativeLabelHodge : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Fin 3 → E) :=
  (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A).transport ((MarkedRationalPeriods.markedRationalPeriodCoordinates A b).trans i.val.1)

def nativeLabelRealization (Q : ComplexMultiplication.CM.Polarization.WeightOnePolarization (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A)) :
    ComplexMultiplication.CMKnownResults.CM.HodgeRealization (nativeLabelHodge A b i) :=
  TypeTransport.hodgeRealizationAlongEquiv ((MarkedRationalPeriods.markedRationalPeriodCoordinates A b).trans i.val.1).symm
    ((AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A).transport_symm_isHodgeMap _)
    ((AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A).transport_isHodgeMap _)
    (IntrinsicPeriodHodge.nativePeriodH1Realization A Q)

theorem nativeLabelRealization_variety (Q : ComplexMultiplication.CM.Polarization.WeightOnePolarization (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A)) :
    (nativeLabelRealization A b i Q).abelianVariety = A := rfl

theorem nativeLabelHodge_holomorphic (hP : P.IsAdmissible) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hperiod : ∀ v : Fin n → ℂ, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b v = 0 ↔
      ClosedCoefficientPeriods.componentPrescribed P i.val.2 (i.normalizer (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) (i.coordinates hP v))
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) :
    x ∈ (nativeLabelHodge A b i).holomorphic ↔
      ClosedCoefficientPeriods.componentPrescribed P i.val.2 (i.normalizer (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) (PeriodCoordinates.cmPeriodCoordinates P hP x) := by
  let a := (MarkedRationalPeriods.markedRationalPeriodCoordinates A b).trans i.val.1
  obtain ⟨u, rfl⟩ := (a.baseChange ℚ ℂ _ _).surjective x
  rw [show (a.baseChange ℚ ℂ _ _) u ∈ (nativeLabelHodge A b i).holomorphic ↔
    u ∈ (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A).holomorphic from
      (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A).transport_holomorphic a u]
  have hi : i.val.1 = (MarkedRationalPeriods.markedRationalPeriodCoordinates A b).symm.trans a := by
    ext v
    simp [a]
  have hc := MarkedCoefficientLabel.marked_coefficient_label_coordinates P hP A b a i hi u
  have hp := hperiod (MarkedRationalPeriods.markedComplexPeriodCoordinates A b u)
  have he : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (MarkedRationalPeriods.markedComplexPeriodCoordinates A b u) =
      AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u := by
    simpa only [LinearEquiv.symm_apply_apply] using
      (MarkedRationalPeriods.markedComplexPeriodCoordinates_projection A b (MarkedRationalPeriods.markedComplexPeriodCoordinates A b u)).symm
  rw [he, hc] at hp
  exact hp

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicLabelRealization
