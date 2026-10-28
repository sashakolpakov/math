import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Ideal.GoingDown

/-! # Prime Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.PrimeExtension.BundleCycles

noncomputable section

/-!
# LineBundleCycles: vertical divisor primes in a polynomial extension

Extending a prime to the polynomial ring preserves its height. A
height-one prime meeting the base nontrivially is exactly that extension.
-/

open _root_.Polynomial

variable {R : Type*} [CommRing R]

theorem polynomialPrimeExtension_comap (p : Ideal R) :
    Ideal.comap (C : R →+* R[X]) (p.map C) = p := by
  ext a
  constructor
  · intro ha
    simpa only [coeff_C_zero] using (Ideal.mem_map_C_iff.mp ha) 0
  · intro ha
    exact Ideal.mem_map_of_mem C ha

theorem polynomialPrimeExtension_height [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] :
    (p.map (C : R →+* R[X])).height = p.height := by
  let : (p.map (C : R →+* R[X])).LiesOver p := ⟨(polynomialPrimeExtension_comap p).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p (p.map (C : R →+* R[X]))
  change (p.map C).height = p.height + ((p.map C).map (Ideal.Quotient.mk (p.map C))).height at h
  simpa only [Ideal.map_quotient_self, Ideal.height_bot, add_zero] using h

theorem polynomialHeightOne_isExtended [IsNoetherianRing R] [IsDomain R]
    (P : Ideal R[X]) [P.IsPrime] (hP : P.height = 1)
    (hp : Ideal.comap (C : R →+* R[X]) P ≠ ⊥) :
    (Ideal.comap (C : R →+* R[X]) P).map C = P := by
  let p := Ideal.comap (C : R →+* R[X]) P
  have hle : p.map C ≤ P := Ideal.map_comap_le
  have hpheight : 1 ≤ p.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hp)
  apply Ideal.eq_of_le_of_height_le (p.map C) hle
  rw [polynomialPrimeExtension_height, hP]
  exact hpheight

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.PrimeExtension.BundleCycles
