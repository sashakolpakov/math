import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PrimeLocalizationUnits
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! # Coordinate Localization Units -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoordinateLocalizationUnits

noncomputable section

/-! On a polynomial chart with one coordinate inverted, every unit
is a nonzero field scalar times an integral power of that coordinate. -/

open _root_.MvPolynomial

universe u v w
variable {K : Type u} [Field K] {σ : Type v}
variable {A : Type w} [CommRing A] [Algebra (MvPolynomial σ K) A]

theorem polynomialCoordinateLocalization_unit_powers (i : σ)
    [IsLocalization.Away (X i : MvPolynomial σ K) A] (z : Aˣ) :
    ∃ (c : Kˣ) (a b : ℕ), (z : A) * algebraMap (MvPolynomial σ K) A (X i) ^ b =
      algebraMap (MvPolynomial σ K) A (C (c : K)) * algebraMap (MvPolynomial σ K) A (X i) ^ a := by
  obtain ⟨c, a, b, h⟩ := PrimeLocalizationUnits.primeLocalization_unit_powers (X i : MvPolynomial σ K) (X_prime (i := i)) z
  obtain ⟨r, hr, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp c.isUnit
  obtain ⟨d, rfl⟩ := hr
  exact ⟨d, a, b, hc ▸ h⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoordinateLocalizationUnits
