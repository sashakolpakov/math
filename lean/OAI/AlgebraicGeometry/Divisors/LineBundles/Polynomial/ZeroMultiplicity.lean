import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeStalk
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.FlatOrderEq

/-! # Zero Multiplicity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroMultiplicity.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual polynomial zero divisor has multiplicity one -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsDomain R]

theorem polynomialCoordinateSection_ne_zero : AffineLine.Space.BundleCycles.polynomialCoordinateSection R ≠ 0 := by
  intro h
  apply Polynomial.X_ne_zero (R := R)
  have hc := congrArg (Scheme.ΓSpecIso (.of (Polynomial R))).hom h
  simpa only [AffineLine.Space.BundleCycles.polynomialCoordinateSection, Iso.inv_hom_id_apply, map_zero] using hc

variable [IsNoetherianRing R]

theorem polynomialZeroDivisor_multiplicity :
    RegularDivisor.BundleCycles.regularFunctionDivisor (Spec (.of (Polynomial R))) (AffineLine.Space.BundleCycles.polynomialCoordinateSection R) (ZeroPrime.BundleCycles.polynomialZeroPrime R) = 1 := by
  rw [RegularDivisor.BundleCycles.regularFunctionDivisor_coeff_length _ _ (polynomialCoordinateSection_ne_zero R) _ (ZeroPrime.BundleCycles.polynomialZeroPrime_coheight R)]
  have hmax := Affine.PrincipalPrimeStalk.BundleCycles.affinePrincipalPrime_stalk_maximalIdeal (ZeroPrime.BundleCycles.polynomialZeroPrime R) Polynomial.X (ZeroPrime.BundleCycles.polynomialZeroPrime_asIdeal R)
  change Ideal.span {(Spec (.of (Polynomial R))).presheaf.germ ⊤ (ZeroPrime.BundleCycles.polynomialZeroPrime R) (by trivial)
      (AffineLine.Space.BundleCycles.polynomialCoordinateSection R)} = _ at hmax
  rw [hmax, FlatOrderEq.BundleCycles.FlatOrder.residue_quotient_length]
  rfl

theorem polynomialZeroDivisor_eq_single :
    RegularDivisor.BundleCycles.regularFunctionDivisor (Spec (.of (Polynomial R))) (AffineLine.Space.BundleCycles.polynomialCoordinateSection R) =
      Finsupp.single (ZeroPrime.BundleCycles.polynomialZeroPrime R) 1 := by
  ext p
  by_cases hp : p = ZeroPrime.BundleCycles.polynomialZeroPrime R
  · subst p
    rw [Finsupp.single_eq_same, polynomialZeroDivisor_multiplicity]
  · rw [Finsupp.single_eq_of_ne hp]
    by_contra hn
    have hs := RegularDivisor.BundleCycles.regularFunctionDivisor_support_subset (Spec (.of (Polynomial R))) (AffineLine.Space.BundleCycles.polynomialCoordinateSection R)
      (Finsupp.mem_support_iff.mpr hn)
    have hh : Order.coheight p = 1 := by
      by_contra h
      exact hn (Scheme.ord_eq_zero_of_coheight_neq_one h _)
    have hX : Polynomial.X ∈ p.asIdeal := by
      change ¬p ∈ (Spec (.of (Polynomial R))).basicOpen ((Scheme.ΓSpecIso (.of (Polynomial R))).inv Polynomial.X) at hs
      rw [basicOpen_eq_of_affine] at hs
      exact not_not.mp hs
    exact hp (ZeroPrime.BundleCycles.polynomialZeroPrime_unique_height_one R p hh hX)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroMultiplicity.BundleCycles
