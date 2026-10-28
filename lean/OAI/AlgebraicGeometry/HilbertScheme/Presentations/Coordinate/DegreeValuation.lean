import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.Algebra.Order.GroupWithZero.WithZero

/-! # Degree Valuation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.DegreeValuation

noncomputable section

/-! Degree in one polynomial coordinate defines a valuation. Its
extension to the function field detects exponents of coordinate ratios. -/

open _root_.MvPolynomial

universe u v
variable {K : Type u} [Field K] {σ : Type v}

def coordinateDegreeValue (i : σ) (f : MvPolynomial σ K) : WithZero (Multiplicative ℤ) := by
  classical
  exact if f = 0 then 0 else ↑(Multiplicative.ofAdd (f.degreeOf i : ℤ) : Multiplicative ℤ)

theorem coordinateDegreeValue_of_ne_zero (i : σ) {f : MvPolynomial σ K} (hf : f ≠ 0) :
    coordinateDegreeValue i f = (↑(Multiplicative.ofAdd (f.degreeOf i : ℤ) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) := by
  classical
  exact ite_eq_right hf

def coordinateDegreeValuation (i : σ) : Valuation (MvPolynomial σ K) (WithZero (Multiplicative ℤ)) where
  toFun := coordinateDegreeValue i
  map_zero' := by simp [coordinateDegreeValue]
  map_one' := by simp [coordinateDegreeValue]
  map_mul' f g := by
    by_cases hf : f = 0
    · subst f
      simp [coordinateDegreeValue]
    by_cases hg : g = 0
    · subst g
      simp [coordinateDegreeValue]
    rw [coordinateDegreeValue_of_ne_zero i (mul_ne_zero hf hg),
      coordinateDegreeValue_of_ne_zero i hf, coordinateDegreeValue_of_ne_zero i hg,
      degreeOf_mul_eq hf hg, Nat.cast_add]
    rfl
  map_add_le_max' f g := by
    by_cases hf : f = 0
    · subst f
      rw [zero_add]
      exact le_max_right _ _
    by_cases hg : g = 0
    · subst g
      rw [add_zero]
      exact le_max_left _ _
    by_cases hfg : f + g = 0
    · rw [hfg]
      simp [coordinateDegreeValue]
    rw [coordinateDegreeValue_of_ne_zero i hfg, coordinateDegreeValue_of_ne_zero i hf,
      coordinateDegreeValue_of_ne_zero i hg]
    apply WithZero.coe_le_coe.mpr
    change ((f + g).degreeOf i : ℤ) ≤ max (f.degreeOf i : ℤ) (g.degreeOf i : ℤ)
    exact_mod_cast degreeOf_add_le i f g

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.DegreeValuation
