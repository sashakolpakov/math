import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalTransitionExponentComparison

/-! # Rational Coordinate Monomials -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalCoordinateMonomials

noncomputable section

/-! Scalar coordinate monomials have exact product, diagonal and
scalar-injectivity laws in the common fraction field. -/

open _root_.MvPolynomial

universe u v
variable {K : Type u} [Field K] {σ : Type v}

theorem rationalProjectiveCoordinate_cocycle (i j k : σ) :
    RationalCoordinateDegrees.rationalProjectiveCoordinate (K := K) i j * RationalCoordinateDegrees.rationalProjectiveCoordinate j k =
      RationalCoordinateDegrees.rationalProjectiveCoordinate i k := by
  unfold RationalCoordinateDegrees.rationalProjectiveCoordinate
  rw [mul_comm]
  exact div_mul_div_cancel₀ (RationalCoordinateDegrees.polynomialFunctionField_ne_zero (X_ne_zero j))

theorem rationalProjectiveCoordinate_self (i : σ) : RationalCoordinateDegrees.rationalProjectiveCoordinate (K := K) i i = 1 :=
  div_self (RationalCoordinateDegrees.polynomialFunctionField_ne_zero (X_ne_zero i))

theorem rationalProjectiveMonomial_cocycle (c e : Kˣ) (i j k : σ) (d : ℤ) :
    RationalTransitionExponentComparison.rationalProjectiveMonomial c i j d * RationalTransitionExponentComparison.rationalProjectiveMonomial e j k d =
      RationalTransitionExponentComparison.rationalProjectiveMonomial (c * e) i k d := by
  unfold RationalTransitionExponentComparison.rationalProjectiveMonomial
  rw [mul_mul_mul_comm, ← mul_zpow, rationalProjectiveCoordinate_cocycle]
  simp only [Units.val_mul, map_mul]

theorem rationalProjectiveMonomial_one_self (i : σ) (d : ℤ) :
    RationalTransitionExponentComparison.rationalProjectiveMonomial (1 : Kˣ) i i d = 1 := by
  simp only [RationalTransitionExponentComparison.rationalProjectiveMonomial, Units.val_one, map_one, rationalProjectiveCoordinate_self,
    one_zpow, mul_one]

theorem rationalProjectiveMonomial_scalar_injective (i j : σ) (d : ℤ) :
    Function.Injective (fun c : Kˣ => RationalTransitionExponentComparison.rationalProjectiveMonomial c i j d) := by
  intro c e h
  apply Units.ext
  apply C_injective
  apply IsFractionRing.injective (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
  exact mul_right_cancel₀ (zpow_ne_zero d (RationalCoordinateDegrees.rationalProjectiveCoordinate_ne_zero i j)) h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalCoordinateMonomials
