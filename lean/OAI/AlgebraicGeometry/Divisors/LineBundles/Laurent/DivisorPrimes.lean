import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.PrimeExtension
import Mathlib.RingTheory.Localization.Submodule

/-! # Divisor Primes -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.DivisorPrimes.BundleCycles

noncomputable section

/-! # LineBundleCycles: all vertical height-one Laurent primes are extended base primes -/

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]

theorem laurentHeightOne_isExtended (P : Ideal (LaurentPolynomial R)) [P.IsPrime]
    (hP : P.height = 1) (hp : P.under R ≠ ⊥) : PrimeExtension.BundleCycles.laurentPrimeExtension (P.under R) = P := by
  let : IsNoetherianRing (LaurentPolynomial R) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (Polynomial.X : Polynomial R))
      (LaurentPolynomial R) inferInstance
  have hle : PrimeExtension.BundleCycles.laurentPrimeExtension (P.under R) ≤ P := by
    rw [PrimeExtension.BundleCycles.laurentPrimeExtension_eq_map]
    exact Ideal.map_comap_le
  have hpheight : 1 ≤ (P.under R).height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hp)
  apply Ideal.eq_of_le_of_height_le (PrimeExtension.BundleCycles.laurentPrimeExtension (P.under R)) hle
  rw [PrimeExtension.BundleCycles.laurentPrimeExtension_height, hP]
  exact hpheight

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.DivisorPrimes.BundleCycles
