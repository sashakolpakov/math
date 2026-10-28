import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingExponential

/-! # Operator Exponential Units -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorExponentialUnits.Construction

noncomputable section

/-! The continuous operator exponential as a unit, with its inverse
and multiplication formulas. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]

def operatorExpUnit (X : L →L[ℝ] L) : (L →L[ℝ] L)ˣ := (Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv X).toUnit

theorem operatorExpUnit_val (X : L →L[ℝ] L) : (operatorExpUnit X : L →L[ℝ] L) = exp X := rfl

theorem operatorExpUnit_inv_val (X : L →L[ℝ] L) : (↑(operatorExpUnit X)⁻¹ : L →L[ℝ] L) = exp (-X) := rfl

theorem operatorExpUnit_zero : operatorExpUnit (0 : L →L[ℝ] L) = 1 := by
  apply Units.ext
  exact exp_zero

theorem operatorExpUnit_neg (X : L →L[ℝ] L) : operatorExpUnit (-X) = (operatorExpUnit X)⁻¹ := by
  apply Units.ext
  rfl

theorem operatorExpUnit_add (X Y : L →L[ℝ] L) (hXY : Commute X Y) :
    operatorExpUnit (X + Y) = operatorExpUnit X * operatorExpUnit Y := by
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  apply Units.ext
  exact exp_add_of_commute hXY

theorem operatorExpUnit_continuous : Continuous (operatorExpUnit (L := L)) := by
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  apply Units.continuous_iff.mpr
  change Continuous (fun X : L →L[ℝ] L => exp X) ∧ Continuous (fun X : L →L[ℝ] L => exp (-X))
  exact ⟨exp_continuous, exp_continuous.comp continuous_neg⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorExponentialUnits.Construction
