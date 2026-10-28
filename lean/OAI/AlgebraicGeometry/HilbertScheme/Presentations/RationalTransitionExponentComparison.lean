import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalCoordinateDegrees

/-! # Rational Transition Exponent Comparison -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalTransitionExponentComparison

noncomputable section

/-! A scalar-coordinate-power cocycle on three distinct projective
coordinates forces its three integer exponents to agree. -/

open _root_.MvPolynomial

universe u v
variable {K : Type u} [Field K] {σ : Type v}

def rationalProjectiveMonomial (c : Kˣ) (i j : σ) (d : ℤ) : FractionRing (MvPolynomial σ K) :=
  algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C (c : K)) *
    RationalCoordinateDegrees.rationalProjectiveCoordinate i j ^ d

theorem rationalProjectiveMonomial_ne_zero (c : Kˣ) (i j : σ) (d : ℤ) :
    rationalProjectiveMonomial c i j d ≠ 0 :=
  mul_ne_zero (RationalCoordinateDegrees.polynomialFunctionField_ne_zero (C_ne_zero.mpr c.ne_zero))
    (zpow_ne_zero d (RationalCoordinateDegrees.rationalProjectiveCoordinate_ne_zero i j))

theorem rationalProjectiveMonomial_degree [DecidableEq σ] (q : σ) (c : Kˣ) (i j : σ) (d : ℤ) :
    RationalCoordinateDegrees.rationalCoordinateDegree q (rationalProjectiveMonomial c i j d) =
      d * ((if q = j then (1 : ℤ) else 0) - (if q = i then (1 : ℤ) else 0)) := by
  unfold rationalProjectiveMonomial
  rw [RationalCoordinateDegrees.rationalCoordinateDegree_mul q _ _ (RationalCoordinateDegrees.polynomialFunctionField_ne_zero (C_ne_zero.mpr c.ne_zero))
    (zpow_ne_zero d (RationalCoordinateDegrees.rationalProjectiveCoordinate_ne_zero i j)),
    RationalCoordinateDegrees.rationalCoordinateDegree_polynomial q (C (c : K)) (C_ne_zero.mpr c.ne_zero), degreeOf_C,
    Nat.cast_zero, zero_add, RationalCoordinateDegrees.rationalCoordinateDegree_zpow, RationalCoordinateDegrees.rationalCoordinateDegree_ratio]

theorem rational_transition_exponents_agree (i j k : σ) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (c d e : Kˣ) (a b r : ℤ)
    (h : rationalProjectiveMonomial c i j a * rationalProjectiveMonomial d j k b =
      rationalProjectiveMonomial e i k r) : a = b ∧ b = r := by
  classical
  have hj := congrArg (RationalCoordinateDegrees.rationalCoordinateDegree j) h
  have hk := congrArg (RationalCoordinateDegrees.rationalCoordinateDegree k) h
  rw [RationalCoordinateDegrees.rationalCoordinateDegree_mul j _ _ (rationalProjectiveMonomial_ne_zero c i j a)
    (rationalProjectiveMonomial_ne_zero d j k b), rationalProjectiveMonomial_degree,
    rationalProjectiveMonomial_degree, rationalProjectiveMonomial_degree] at hj
  rw [RationalCoordinateDegrees.rationalCoordinateDegree_mul k _ _ (rationalProjectiveMonomial_ne_zero c i j a)
    (rationalProjectiveMonomial_ne_zero d j k b), rationalProjectiveMonomial_degree,
    rationalProjectiveMonomial_degree, rationalProjectiveMonomial_degree] at hk
  simp [hij.symm, hjk] at hj
  simp [hjk.symm, hik.symm] at hk
  exact ⟨by omega, hk⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalTransitionExponentComparison
