import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Projection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ExtendedPrimeStalk
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiberDivisorZero

/-! # Divisor Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DivisorPullback.BundleCycles

noncomputable section

/-!
# LineBundleCycles: complete rational-divisor pullback to the affine line
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem polynomialProjection_order (p : Spec (CommRingCat.of R))
    (g : (Spec (CommRingCat.of R)).functionField) :
    (Spec (CommRingCat.of (Polynomial R))).ord (Projection.BundleCycles.polynomialFunctionFieldMap R g) (Projection.BundleCycles.polynomialPrimePoint R p) =
      (Spec (CommRingCat.of R)).ord g p := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  by_cases hp : coheight p = 1
  · have hP : ((Projection.BundleCycles.polynomialPrimePoint R p).asIdeal.under R).map
        (algebraMap R (Polynomial R)) = (Projection.BundleCycles.polynomialPrimePoint R p).asIdeal := by
      change (Ideal.comap (Polynomial.C : R →+* Polynomial R) (p.asIdeal.map Polynomial.C)).map Polynomial.C =
        p.asIdeal.map Polynomial.C
      rw [PrimeExtension.BundleCycles.polynomialPrimeExtension_comap]
    have hmax := Affine.ExtendedPrimeStalk.BundleCycles.affineExtendedPrime_stalk_maximalIdeal (Projection.BundleCycles.polynomialPrimePoint R p) hP
    have h := FlatMorphismOrder.BundleCycles.ord_flat_stalk_eq (Projection.BundleCycles.polynomialProjection R) (Projection.BundleCycles.polynomialProjection_genericPoint R)
      (Projection.BundleCycles.polynomialPrimePoint R p) ((Projection.BundleCycles.polynomialPrimePoint_coheight R p).trans hp)
      (by rw [Projection.BundleCycles.polynomialPrimePoint_projection]; exact hp) hmax g
    exact h.trans (congrArg ((Spec (CommRingCat.of R)).ord g) (Projection.BundleCycles.polynomialPrimePoint_projection R p))
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hp,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hp ((Projection.BundleCycles.polynomialPrimePoint_coheight R p).symm.trans h))]

theorem polynomialPulledDivisor_support (g : (Spec (CommRingCat.of R)).functionField) (hg : g ≠ 0)
    (P : Spec (CommRingCat.of (Polynomial R)))
    (hP : (Spec (CommRingCat.of (Polynomial R))).ord (Projection.BundleCycles.polynomialFunctionFieldMap R g) P ≠ 0) :
    P ∈ Set.range (Projection.BundleCycles.polynomialPrimePoint R) := by
  let : P.asIdeal.IsPrime := (show PrimeSpectrum (Polynomial R) from P).isPrime
  have hheight : P.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight]
    by_contra hn
    exact hP (Scheme.ord_eq_zero_of_coheight_neq_one hn _)
  have hp : P.asIdeal.under R ≠ ⊥ := by
    intro hp
    apply hP
    apply GenericFiberDivisorZero.BundleCycles.ord_pullback_zero_over_generic (Projection.BundleCycles.polynomialProjection R) (Projection.BundleCycles.polynomialProjection_genericPoint R) g hg P
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hp
  refine ⟨Projection.BundleCycles.polynomialProjection R P, ?_⟩
  exact PrimeSpectrum.ext (PrimeExtension.BundleCycles.polynomialHeightOne_isExtended P.asIdeal hheight hp)

def polynomialCycleExtension : (Spec (CommRingCat.of R) →₀ ℚ) →ₗ[ℚ]
    (Spec (CommRingCat.of (Polynomial R)) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (Projection.BundleCycles.polynomialPrimePoint R)

theorem polynomialPrincipalDivisor_pullback (g : (Spec (CommRingCat.of R)).functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of (Polynomial R))) (Projection.BundleCycles.polynomialFunctionFieldMap R g) =
      polynomialCycleExtension R (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of R)) g) := by
  ext P
  by_cases hP : P ∈ Set.range (Projection.BundleCycles.polynomialPrimePoint R)
  · obtain ⟨p, rfl⟩ := hP
    change _ = Finsupp.mapDomain (Projection.BundleCycles.polynomialPrimePoint R) _ (Projection.BundleCycles.polynomialPrimePoint R p)
    rw [Finsupp.mapDomain_apply_of_injective (Projection.BundleCycles.polynomialPrimePoint_injective R),
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, polynomialProjection_order]
  · have hz : (Spec (CommRingCat.of (Polynomial R))).ord (Projection.BundleCycles.polynomialFunctionFieldMap R g) P = 0 := by
      by_contra hn
      exact hP (polynomialPulledDivisor_support R g hg P hn)
    change _ = Finsupp.mapDomain (Projection.BundleCycles.polynomialPrimePoint R) _ P
    rw [Finsupp.mapDomain_of_notMem_range _ _ hP, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, hz, Int.cast_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DivisorPullback.BundleCycles
