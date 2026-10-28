import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.PrimeExtension
import Mathlib.Algebra.Polynomial.Laurent

/-! # Prime Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.PrimeExtension.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual Laurent extensions of prime supports
-/

open _root_.Polynomial

variable {R : Type*} [CommRing R]

theorem polynomialPrimeExtension_disjoint_X (p : Ideal R) [p.IsPrime] :
    Disjoint (Submonoid.powers (X : R[X]) : Set R[X]) (p.map C : Set R[X]) := by
  apply (Ideal.disjoint_powers_iff_notMem_of_isPrime X).mpr
  intro h
  have h1 := Ideal.mem_map_C_iff.mp h 1
  rw [coeff_X_one] at h1
  exact (show p ≠ ⊤ from Ideal.IsPrime.ne_top') ((Ideal.eq_top_iff_one p).mpr h1)

def laurentPrimeExtension (p : Ideal R) : Ideal (LaurentPolynomial R) :=
  (p.map (C : R →+* R[X])).map (algebraMap R[X] (LaurentPolynomial R))

instance laurentPrimeExtension_isPrime (p : Ideal R) [p.IsPrime] :
    (laurentPrimeExtension p).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (X : R[X])) (LaurentPolynomial R)
    (p.map C) inferInstance (polynomialPrimeExtension_disjoint_X p)

theorem laurentPrimeExtension_under_polynomial (p : Ideal R) [p.IsPrime] :
    (laurentPrimeExtension p).under R[X] = p.map C :=
  IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (X : R[X])) (LaurentPolynomial R)
    inferInstance (polynomialPrimeExtension_disjoint_X p)

theorem laurentPrimeExtension_eq_map (p : Ideal R) :
    laurentPrimeExtension p = p.map (algebraMap R (LaurentPolynomial R)) := by
  rw [laurentPrimeExtension, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro r
  exact Polynomial.toLaurent_C r

theorem laurentPrimeExtension_under (p : Ideal R) [p.IsPrime] :
    (laurentPrimeExtension p).under R = p := by
  have hc : (algebraMap R[X] (LaurentPolynomial R)).comp (C : R →+* R[X]) =
      algebraMap R (LaurentPolynomial R) := by
    apply RingHom.ext
    intro r
    exact Polynomial.toLaurent_C r
  change Ideal.comap (algebraMap R (LaurentPolynomial R)) (laurentPrimeExtension p) = p
  rw [← hc, ← Ideal.comap_comap]
  exact (congrArg (Ideal.comap (C : R →+* R[X])) (laurentPrimeExtension_under_polynomial p)).trans
    (LineBundles.Polynomial.PrimeExtension.BundleCycles.polynomialPrimeExtension_comap p)

theorem laurentPrimeExtension_height [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] :
    (laurentPrimeExtension p).height = p.height :=
  (IsLocalization.height_map_of_disjoint (S := LaurentPolynomial R) (Submonoid.powers (X : R[X]))
    (p.map C) (polynomialPrimeExtension_disjoint_X p)).trans (LineBundles.Polynomial.PrimeExtension.BundleCycles.polynomialPrimeExtension_height p)

theorem laurentPrimeExtension_injective : Function.Injective (fun p : PrimeSpectrum R =>
    (⟨laurentPrimeExtension p.asIdeal, laurentPrimeExtension_isPrime p.asIdeal⟩ : PrimeSpectrum (LaurentPolynomial R))) := by
  intro p q h
  apply PrimeSpectrum.ext
  have hc := congrArg (fun P : PrimeSpectrum (LaurentPolynomial R) => P.asIdeal.under R) h
  simpa only [laurentPrimeExtension_under] using hc

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.PrimeExtension.BundleCycles
