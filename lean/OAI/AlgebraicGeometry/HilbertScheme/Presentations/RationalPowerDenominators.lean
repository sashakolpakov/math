import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-! # Rational Power Denominators -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalPowerDenominators

/-! A scalar-power equation with cleared denominators determines the
corresponding rational function with its integral exponent. -/

universe u
variable {F : Type u} [Field F]

theorem rational_power_of_cleared_denominator (z c q : F) (hq : q ≠ 0) (a b : ℕ)
    (h : z * q ^ b = c * q ^ a) : z = c * q ^ ((a : ℤ) - b) := by
  calc
    z = (c * q ^ a) / q ^ b := (eq_div_iff_mul_eq (pow_ne_zero b hq)).mpr h
    _ = c * q ^ ((a : ℤ) - b) := by
      rw [zpow_sub₀ hq, zpow_natCast, zpow_natCast, mul_div_assoc]

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalPowerDenominators
