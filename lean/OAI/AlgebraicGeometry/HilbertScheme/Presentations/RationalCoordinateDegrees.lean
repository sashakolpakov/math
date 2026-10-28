import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.FunctionFieldValuation

/-! # Rational Coordinate Degrees -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalCoordinateDegrees

noncomputable section

/-! Integer coordinate degrees of rational functions, with exact
product, inverse, power, scalar and coordinate-ratio formulas. -/

open _root_.MvPolynomial

universe u v
variable {K : Type u} [Field K] {σ : Type v}

def rationalCoordinateDegree (i : σ) (f : FractionRing (MvPolynomial σ K)) : ℤ :=
  WithZero.log (Coordinate.FunctionFieldValuation.coordinateFunctionFieldValuation i f)

theorem rationalCoordinateDegree_mul (i : σ) (f g : FractionRing (MvPolynomial σ K))
    (hf : f ≠ 0) (hg : g ≠ 0) :
    rationalCoordinateDegree i (f * g) = rationalCoordinateDegree i f + rationalCoordinateDegree i g := by
  unfold rationalCoordinateDegree
  rw [map_mul, WithZero.log_mul ((Coordinate.FunctionFieldValuation.coordinateFunctionFieldValuation i).ne_zero_iff.mpr hf)
    ((Coordinate.FunctionFieldValuation.coordinateFunctionFieldValuation i).ne_zero_iff.mpr hg)]

theorem rationalCoordinateDegree_div (i : σ) (f g : FractionRing (MvPolynomial σ K))
    (hf : f ≠ 0) (hg : g ≠ 0) :
    rationalCoordinateDegree i (f / g) = rationalCoordinateDegree i f - rationalCoordinateDegree i g := by
  unfold rationalCoordinateDegree
  rw [map_div₀, WithZero.log_div ((Coordinate.FunctionFieldValuation.coordinateFunctionFieldValuation i).ne_zero_iff.mpr hf)
    ((Coordinate.FunctionFieldValuation.coordinateFunctionFieldValuation i).ne_zero_iff.mpr hg)]

theorem rationalCoordinateDegree_zpow (i : σ) (f : FractionRing (MvPolynomial σ K)) (d : ℤ) :
    rationalCoordinateDegree i (f ^ d) = d * rationalCoordinateDegree i f := by
  unfold rationalCoordinateDegree
  rw [map_zpow₀, WithZero.log_zpow]
  rfl

theorem rationalCoordinateDegree_polynomial (i : σ) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    rationalCoordinateDegree i (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) f) =
      (f.degreeOf i : ℤ) := by
  unfold rationalCoordinateDegree
  rw [Coordinate.FunctionFieldValuation.coordinateFunctionFieldValuation_polynomial]
  change WithZero.log (Coordinate.DegreeValuation.coordinateDegreeValue i f) = _
  rw [Coordinate.DegreeValuation.coordinateDegreeValue_of_ne_zero i hf]
  rfl

def rationalProjectiveCoordinate (i j : σ) : FractionRing (MvPolynomial σ K) :=
  algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (X j) /
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (X i)

theorem polynomialFunctionField_ne_zero {f : MvPolynomial σ K} (hf : f ≠ 0) :
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) f ≠ 0 :=
  IsFractionRing.to_map_eq_zero_iff.not.mpr hf

theorem rationalProjectiveCoordinate_ne_zero (i j : σ) : rationalProjectiveCoordinate (K := K) i j ≠ 0 := by
  apply div_ne_zero
  · exact polynomialFunctionField_ne_zero (X_ne_zero j)
  · exact polynomialFunctionField_ne_zero (X_ne_zero i)

theorem rationalCoordinateDegree_ratio (q i j : σ) [DecidableEq σ] :
    rationalCoordinateDegree q (rationalProjectiveCoordinate (K := K) i j) =
      (if q = j then (1 : ℤ) else 0) - (if q = i then (1 : ℤ) else 0) := by
  unfold rationalProjectiveCoordinate
  rw [rationalCoordinateDegree_div q _ _
    (polynomialFunctionField_ne_zero (X_ne_zero j))
    (polynomialFunctionField_ne_zero (X_ne_zero i)),
    rationalCoordinateDegree_polynomial q (X j) (X_ne_zero j),
    rationalCoordinateDegree_polynomial q (X i) (X_ne_zero i), degreeOf_X, degreeOf_X]
  split_ifs <;> rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalCoordinateDegrees
