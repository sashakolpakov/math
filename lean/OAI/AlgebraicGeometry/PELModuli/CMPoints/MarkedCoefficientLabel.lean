import OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedComplexCoordinates
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RationalCoefficientLabels

/-! # Marked Coefficient Label -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedCoefficientLabel

noncomputable section

/-! The countable coefficient label agrees exactly with the complex
coordinates of the actual marked native period lattice. -/

open scoped Classical

theorem marked_coefficient_label_coordinates
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s n : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin n) A)
    (a : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] (Fin 3 → E)) (i : RationalCoefficientLabels.RationalCoefficientLabel P n)
    (hi : i.val.1 = (MarkedRationalPeriods.markedRationalPeriodCoordinates A b).symm.trans a)
    (u : ComplexMultiplication.WeightOne.CM.Complexification (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    i.coordinates hP (MarkedRationalPeriods.markedComplexPeriodCoordinates A b u) =
      PeriodCoordinates.cmPeriodCoordinates P hP ((a.baseChange ℚ ℂ _ _) u) := by
  rw [MarkedComplexCoordinates.marked_complex_coordinates_baseChange]
  change PeriodCoordinates.cmPeriodCoordinates P hP ((i.val.1.baseChange ℚ ℂ _ _)
    ((TensorProduct.piScalarRight ℚ ℂ ℂ (Fin n)).symm
      (TensorProduct.piScalarRight ℚ ℂ ℂ (Fin n)
        (((MarkedRationalPeriods.markedRationalPeriodCoordinates A b).baseChange ℚ ℂ _ _) u)))) = _
  rw [LinearEquiv.symm_apply_apply, hi, LinearEquiv.baseChange_trans, LinearEquiv.baseChange_symm]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedCoefficientLabel
