import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.DegreeValuation
import Mathlib.RingTheory.Localization.FractionRing

/-! # Function Field Valuation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.FunctionFieldValuation

noncomputable section

/-! Coordinate-degree valuations extend to the polynomial function
field and evaluate coordinate ratios by the difference of their exponents. -/

open _root_.MvPolynomial
open scoped nonZeroDivisors

universe u v
variable {K : Type u} [Field K] {σ : Type v}

theorem coordinateDegreeValuation_ne_zero_iff (i : σ) (f : MvPolynomial σ K) :
    DegreeValuation.coordinateDegreeValuation i f ≠ 0 ↔ f ≠ 0 := by
  classical
  by_cases h : f = 0
  · subst f
    simp
  · change DegreeValuation.coordinateDegreeValue i f ≠ 0 ↔ _
    rw [DegreeValuation.coordinateDegreeValue_of_ne_zero i h]
    exact iff_of_true (WithZero.coe_ne_zero) h

def coordinateFunctionFieldValuation (i : σ) :
    Valuation (FractionRing (MvPolynomial σ K)) (WithZero (Multiplicative ℤ)) :=
  (DegreeValuation.coordinateDegreeValuation i).extendToLocalization (S := (MvPolynomial σ K)⁰)
    (by
      intro f hf
      change DegreeValuation.coordinateDegreeValuation i f ≠ 0
      exact (coordinateDegreeValuation_ne_zero_iff i f).mpr (nonZeroDivisors.ne_zero hf))
    (FractionRing (MvPolynomial σ K))

theorem coordinateFunctionFieldValuation_polynomial (i : σ) (f : MvPolynomial σ K) :
    coordinateFunctionFieldValuation i (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) f) =
      DegreeValuation.coordinateDegreeValuation i f :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ f

theorem coordinateFunctionFieldValuation_constant (i : σ) (c : K) (hc : c ≠ 0) :
    coordinateFunctionFieldValuation i
      (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C c)) = 1 := by
  rw [coordinateFunctionFieldValuation_polynomial]
  change DegreeValuation.coordinateDegreeValue i (C c) = 1
  rw [DegreeValuation.coordinateDegreeValue_of_ne_zero i (C_ne_zero.mpr hc), degreeOf_C]
  rfl

theorem coordinateFunctionFieldValuation_variable (i j : σ) [DecidableEq σ] :
    coordinateFunctionFieldValuation (K := K) i
      (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (X j)) =
        (↑(Multiplicative.ofAdd (if i = j then (1 : ℤ) else 0) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [coordinateFunctionFieldValuation_polynomial]
  change DegreeValuation.coordinateDegreeValue i (X j) = _
  rw [DegreeValuation.coordinateDegreeValue_of_ne_zero i (X_ne_zero j), degreeOf_X]
  split_ifs <;> rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.FunctionFieldValuation
