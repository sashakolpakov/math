import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Exponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.MultiplicativeMeasurableSpace

/-! # Exponential Linear Character -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialLinearCharacter.Construction

noncomputable section

/-! A real linear functional exponentiates to a positive measurable
character of its additive group, written multiplicatively. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure
open scoped ENNReal

def exponentialLinearCharacter {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ₗ[ℝ] ℝ) : Multiplicative E →* ℝ≥0∞ where
  toFun x := ENNReal.ofReal (Real.exp (f x.toAdd))
  map_one' := by simp
  map_mul' x y := by
    change ENNReal.ofReal (Real.exp (f (x.toAdd + y.toAdd))) = _
    rw [map_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]

theorem exponentialLinearCharacter_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] ℝ) : Continuous (exponentialLinearCharacter f) :=
  ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp f.continuous_of_finiteDimensional)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialLinearCharacter.Construction
