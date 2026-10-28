import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.FiberGenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ExtendedPrimeStalk
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiberDivisorZero

/-! # Divisor Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.DivisorPullback.BundleCycles

noncomputable section

/-!
# LineBundleCycles: complete rational-divisor pullback to the punctured affine line
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem laurentProjection_order (p : Spec (CommRingCat.of R))
    (g : (Spec (CommRingCat.of R)).functionField) :
    (Spec (CommRingCat.of (LaurentPolynomial R))).ord (FiberGenericPoint.BundleCycles.laurentFunctionFieldMap R g) (FiberGenericPoint.BundleCycles.laurentPrimePoint R p) =
      (Spec (CommRingCat.of R)).ord g p := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  by_cases hp : coheight p = 1
  · have hP : ((FiberGenericPoint.BundleCycles.laurentPrimePoint R p).asIdeal.under R).map
        (algebraMap R (LaurentPolynomial R)) = (FiberGenericPoint.BundleCycles.laurentPrimePoint R p).asIdeal := by
      change ((PrimeExtension.BundleCycles.laurentPrimeExtension p.asIdeal).under R).map _ = PrimeExtension.BundleCycles.laurentPrimeExtension p.asIdeal
      rw [PrimeExtension.BundleCycles.laurentPrimeExtension_under]
      exact (PrimeExtension.BundleCycles.laurentPrimeExtension_eq_map p.asIdeal).symm
    have hmax := Affine.ExtendedPrimeStalk.BundleCycles.affineExtendedPrime_stalk_maximalIdeal (FiberGenericPoint.BundleCycles.laurentPrimePoint R p) hP
    have h := FlatMorphismOrder.BundleCycles.ord_flat_stalk_eq (FiberGenericPoint.BundleCycles.laurentProjection R) (FiberGenericPoint.BundleCycles.laurentProjection_genericPoint R)
      (FiberGenericPoint.BundleCycles.laurentPrimePoint R p) ((FiberGenericPoint.BundleCycles.laurentPrimePoint_coheight R p).trans hp)
      (by rw [FiberGenericPoint.BundleCycles.laurentPrimePoint_projection]; exact hp) hmax g
    exact h.trans (congrArg ((Spec (CommRingCat.of R)).ord g) (FiberGenericPoint.BundleCycles.laurentPrimePoint_projection R p))
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hp,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hp ((FiberGenericPoint.BundleCycles.laurentPrimePoint_coheight R p).symm.trans h))]

theorem laurentPulledDivisor_support (g : (Spec (CommRingCat.of R)).functionField) (hg : g ≠ 0)
    (P : Spec (CommRingCat.of (LaurentPolynomial R)))
    (hP : (Spec (CommRingCat.of (LaurentPolynomial R))).ord (FiberGenericPoint.BundleCycles.laurentFunctionFieldMap R g) P ≠ 0) :
    P ∈ Set.range (FiberGenericPoint.BundleCycles.laurentPrimePoint R) := by
  let : P.asIdeal.IsPrime := (show PrimeSpectrum (LaurentPolynomial R) from P).isPrime
  have hheight : P.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight]
    by_contra hn
    exact hP (Scheme.ord_eq_zero_of_coheight_neq_one hn _)
  have hp : P.asIdeal.under R ≠ ⊥ := by
    intro hp
    apply hP
    apply GenericFiberDivisorZero.BundleCycles.ord_pullback_zero_over_generic (FiberGenericPoint.BundleCycles.laurentProjection R) (FiberGenericPoint.BundleCycles.laurentProjection_genericPoint R) g hg P
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hp
  refine ⟨FiberGenericPoint.BundleCycles.laurentProjection R P, ?_⟩
  exact PrimeSpectrum.ext (DivisorPrimes.BundleCycles.laurentHeightOne_isExtended P.asIdeal hheight hp)

def laurentCycleExtension : (Spec (CommRingCat.of R) →₀ ℚ) →ₗ[ℚ]
    (Spec (CommRingCat.of (LaurentPolynomial R)) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (FiberGenericPoint.BundleCycles.laurentPrimePoint R)

theorem laurentPrincipalDivisor_pullback (g : (Spec (CommRingCat.of R)).functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of (LaurentPolynomial R))) (FiberGenericPoint.BundleCycles.laurentFunctionFieldMap R g) =
      laurentCycleExtension R (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of R)) g) := by
  ext P
  by_cases hP : P ∈ Set.range (FiberGenericPoint.BundleCycles.laurentPrimePoint R)
  · obtain ⟨p, rfl⟩ := hP
    change _ = Finsupp.mapDomain (FiberGenericPoint.BundleCycles.laurentPrimePoint R) _ (FiberGenericPoint.BundleCycles.laurentPrimePoint R p)
    rw [Finsupp.mapDomain_apply_of_injective (FiberGenericPoint.BundleCycles.laurentPrimePoint_injective R),
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, laurentProjection_order]
  · have hz : (Spec (CommRingCat.of (LaurentPolynomial R))).ord (FiberGenericPoint.BundleCycles.laurentFunctionFieldMap R g) P = 0 := by
      by_contra hn
      exact hP (laurentPulledDivisor_support R g hg P hn)
    change _ = Finsupp.mapDomain (FiberGenericPoint.BundleCycles.laurentPrimePoint R) _ P
    rw [Finsupp.mapDomain_of_notMem_range _ _ hP, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, hz, Int.cast_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.DivisorPullback.BundleCycles
