import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroSection
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Zero Prime -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroPrime.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual generic point of the polynomial zero divisor has height one -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsDomain R]

def polynomialZeroPrime : Spec (.of (Polynomial R)) := ZeroSection.BundleCycles.polynomialZeroSection R (genericPoint (Spec (.of R)))

theorem polynomialZeroPrime_asIdeal : (polynomialZeroPrime R).asIdeal = Ideal.span {Polynomial.X} := by
  change (PrimeSpectrum.comap (Polynomial.constantCoeff : Polynomial R →+* R)
    (genericPoint (Spec (.of R)))).asIdeal = _
  rw [genericPoint_eq_bot_of_affine]
  exact Polynomial.ker_constantCoeff

theorem polynomialZeroPrime_coheight [IsNoetherianRing R] : Order.coheight (polynomialZeroPrime R) = 1 := by
  rw [← idealHeight_eq_coheight, polynomialZeroPrime_asIdeal]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr Polynomial.X_ne_zero) Polynomial.not_isUnit_X

theorem polynomialZeroPrime_unique_height_one [IsNoetherianRing R] (p : Spec (.of (Polynomial R)))
    (hp : Order.coheight p = 1) (hX : Polynomial.X ∈ p.asIdeal) : p = polynomialZeroPrime R := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum (Polynomial R) from p).isPrime
  let : (polynomialZeroPrime R).asIdeal.IsPrime := (show PrimeSpectrum (Polynomial R) from polynomialZeroPrime R).isPrime
  have hle : (polynomialZeroPrime R).asIdeal ≤ p.asIdeal := by
    rw [polynomialZeroPrime_asIdeal]
    exact (Ideal.span_singleton_le_iff_mem (I := p.asIdeal)).mpr hX
  apply PrimeSpectrum.ext
  apply Eq.symm
  apply Ideal.eq_of_le_of_height_le (polynomialZeroPrime R).asIdeal hle
  rw [idealHeight_eq_coheight, idealHeight_eq_coheight, hp, polynomialZeroPrime_coheight]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroPrime.BundleCycles
