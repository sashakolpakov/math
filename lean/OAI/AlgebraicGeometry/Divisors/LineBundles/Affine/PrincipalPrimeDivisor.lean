import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeStalk
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.FlatOrderEq

/-! # Principal Prime Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: an actual nonzero principal prime has exactly its reduced single-point divisor -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p : Spec (.of R)) (a : R) (hp : p.asIdeal = Ideal.span {a}) (ha : a ≠ 0)

include hp ha

theorem affinePrincipalPrime_coheight : Order.coheight p = 1 := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  have hunit : ¬IsUnit a := by
    intro h
    apply (show p.asIdeal ≠ ⊤ from Ideal.IsPrime.ne_top')
    apply p.asIdeal.eq_top_of_isUnit_mem _ h
    rw [hp]
    exact Ideal.subset_span (Set.mem_singleton a)
  rw [← idealHeight_eq_coheight, hp]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr ha) hunit

theorem affinePrincipalPrime_multiplicity :
    RegularDivisor.BundleCycles.regularFunctionDivisor (Spec (.of R)) ((Scheme.ΓSpecIso (.of R)).inv a) p = 1 := by
  have hs : (Scheme.ΓSpecIso (.of R)).inv a ≠ 0 :=
    (map_ne_zero_iff _ (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.injective).mpr ha
  rw [RegularDivisor.BundleCycles.regularFunctionDivisor_coeff_length _ _ hs _ (affinePrincipalPrime_coheight p a hp ha),
    PrincipalPrimeStalk.BundleCycles.affinePrincipalPrime_stalk_maximalIdeal p a hp, FlatOrderEq.BundleCycles.FlatOrder.residue_quotient_length]
  rfl

theorem affinePrincipalPrime_divisor :
    RegularDivisor.BundleCycles.regularFunctionDivisor (Spec (.of R)) ((Scheme.ΓSpecIso (.of R)).inv a) = Finsupp.single p 1 := by
  ext q
  by_cases hq : q = p
  · subst q
    rw [Finsupp.single_eq_same, affinePrincipalPrime_multiplicity p a hp ha]
  · rw [Finsupp.single_eq_of_ne hq]
    by_contra hn
    have hs := RegularDivisor.BundleCycles.regularFunctionDivisor_support_subset (Spec (.of R)) ((Scheme.ΓSpecIso (.of R)).inv a)
      (Finsupp.mem_support_iff.mpr hn)
    have hh : Order.coheight q = 1 := by
      by_contra h
      exact hn (Scheme.ord_eq_zero_of_coheight_neq_one h _)
    have hmem : a ∈ q.asIdeal := by
      change ¬q ∈ (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv a) at hs
      rw [basicOpen_eq_of_affine] at hs
      exact not_not.mp hs
    have hle : p.asIdeal ≤ q.asIdeal := by
      rw [hp]
      exact (Ideal.span_singleton_le_iff_mem (I := q.asIdeal)).mpr hmem
    let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
    let : q.asIdeal.IsPrime := (show PrimeSpectrum R from q).isPrime
    apply hq
    apply PrimeSpectrum.ext
    apply Eq.symm
    apply Ideal.eq_of_le_of_height_le p.asIdeal hle
    rw [idealHeight_eq_coheight, idealHeight_eq_coheight, hh, affinePrincipalPrime_coheight p a hp ha]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeDivisor.BundleCycles
