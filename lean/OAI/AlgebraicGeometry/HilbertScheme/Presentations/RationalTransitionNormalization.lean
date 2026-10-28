import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalCoordinateMonomials

/-! # Rational Transition Normalization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalTransitionNormalization

noncomputable section

/-! Rescaling by a base row of a scalar cocycle removes exactly the
scalar factors of rational coordinate monomials. -/

open _root_.MvPolynomial

universe u v
variable {K : Type u} [Field K] {σ : Type v}

theorem rationalProjectiveMonomial_normalize (c e q : Kˣ) (h : c * q = e) (i j : σ) (d : ℤ) :
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C (c : K)) *
      RationalTransitionExponentComparison.rationalProjectiveMonomial q i j d *
        algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C ((e⁻¹ : Kˣ) : K)) =
      RationalCoordinateDegrees.rationalProjectiveCoordinate i j ^ d := by
  have hu : c * q * e⁻¹ = 1 := by rw [h, mul_inv_cancel]
  have hv := congrArg (fun a : Kˣ =>
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C (a : K))) hu
  simp only [Units.val_mul, Units.val_one, map_mul, map_one] at hv
  unfold RationalTransitionExponentComparison.rationalProjectiveMonomial
  calc
    _ = (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C (c : K)) *
        algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C (q : K)) *
        algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (C ((e⁻¹ : Kˣ) : K))) *
          RationalCoordinateDegrees.rationalProjectiveCoordinate i j ^ d := by ac_rfl
    _ = _ := by rw [hv, one_mul]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalTransitionNormalization
