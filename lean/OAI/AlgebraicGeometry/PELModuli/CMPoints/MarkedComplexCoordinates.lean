import OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedRationalPeriods
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Marked Complex Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedComplexCoordinates

noncomputable section

/-! Complexifying the rational coordinates of an arbitrary native
integral marking gives exactly its marked complex period coordinates. -/

open scoped TensorProduct
open scoped Classical

theorem basis_complex_coordinates {I U : Type} [Fintype I]
    [AddCommGroup U] [Module ℚ U] (b : Module.Basis I ℚ U)
    (u : ComplexMultiplication.WeightOne.CM.Complexification U) :
    (b.baseChange ℂ).equivFun u =
      TensorProduct.piScalarRight ℚ ℂ ℂ I ((b.equivFun.baseChange ℚ ℂ _ _) u) := by
  induction u using TensorProduct.inductionOn with
  | tmul z v =>
    ext i
    change (b.baseChange ℂ).repr (z ⊗ₜ[ℚ] v) i = _
    rw [Module.Basis.baseChange_repr_tmul]
    rfl
  | add u v hu hv => simp only [map_add, hu, hv]

theorem marked_complex_coordinates_baseChange {I : Type} [Fintype I]
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking I A)
    (u : ComplexMultiplication.WeightOne.CM.Complexification (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    MarkedRationalPeriods.markedComplexPeriodCoordinates A b u =
      TensorProduct.piScalarRight ℚ ℂ ℂ I
        (((MarkedRationalPeriods.markedRationalPeriodCoordinates A b).baseChange ℚ ℂ _ _) u) :=
  basis_complex_coordinates (MarkedRationalPeriods.markedRationalPeriodBasis A b) u

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.MarkedComplexCoordinates
