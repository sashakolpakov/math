import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.AffinePrimePoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ExtendedPrimeStalk
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiberDivisorZero

/-! # Affine Divisor Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.AffineDivisorPullback.BundleCycles

noncomputable section

/-! Pullback of rational principal divisors along the actual smooth affine
projection with geometrically integral fibers. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDomain S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Smooth (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S)]
    [GeometricallyIntegral (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S)]

theorem geometricAffineProjection_order (p : Spec (.of R)) (g : (Spec (.of R)).functionField) :
    (Spec (.of S)).ord (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S) g)
        (AffinePrimePoint.BundleCycles.geometricAffinePrimePoint R S p) = (Spec (.of R)).ord g p := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  by_cases hp : coheight p = 1
  · have hP : ((AffinePrimePoint.BundleCycles.geometricAffinePrimePoint R S p).asIdeal.under R).map
        (algebraMap R S) = (AffinePrimePoint.BundleCycles.geometricAffinePrimePoint R S p).asIdeal := by
      change (Ideal.comap (algebraMap R S) (p.asIdeal.map (algebraMap R S))).map
        (algebraMap R S) = p.asIdeal.map (algebraMap R S)
      rw [AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection_comap_map]
    have hmax := Affine.ExtendedPrimeStalk.BundleCycles.affineExtendedPrime_stalk_maximalIdeal (AffinePrimePoint.BundleCycles.geometricAffinePrimePoint R S p) hP
    have h := FlatMorphismOrder.BundleCycles.ord_flat_stalk_eq (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S)
      (Integral.FiberFieldNaturality.BundleCycles.integralFiberProjection_genericPoint (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S))
      (AffinePrimePoint.BundleCycles.geometricAffinePrimePoint R S p) ((AffinePrimePoint.BundleCycles.geometricAffinePrimePoint_coheight R S p).trans hp)
      (by rw [AffinePrimePoint.BundleCycles.geometricAffinePrimePoint_projection]; exact hp) hmax g
    exact h.trans (congrArg ((Spec (.of R)).ord g) (AffinePrimePoint.BundleCycles.geometricAffinePrimePoint_projection R S p))
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hp,
      Scheme.ord_eq_zero_of_coheight_neq_one
        (fun h => hp ((AffinePrimePoint.BundleCycles.geometricAffinePrimePoint_coheight R S p).symm.trans h))]

theorem geometricAffinePulledDivisor_support (g : (Spec (.of R)).functionField) (hg : g ≠ 0)
    (P : Spec (.of S))
    (hP : (Spec (.of S)).ord (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S) g) P ≠ 0) :
    P ∈ Set.range (AffinePrimePoint.BundleCycles.geometricAffinePrimePoint R S) := by
  let : P.asIdeal.IsPrime := (show PrimeSpectrum S from P).isPrime
  let : (P.asIdeal.comap (algebraMap R S)).IsPrime := inferInstance
  let : ((P.asIdeal.comap (algebraMap R S)).map (algebraMap R S)).IsPrime :=
    AffinePrimeExtension.BundleCycles.geometricAffine_primeExtension R S _
  let : Module.Flat R S := RingHom.flat_algebraMap_iff.mp
    ((Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap R S))).mp
      (inferInstanceAs (Flat (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S))))
  have hheight : P.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight]
    by_contra hn
    exact hP (Scheme.ord_eq_zero_of_coheight_neq_one hn _)
  have hp : P.asIdeal.under R ≠ ⊥ := by
    intro hp
    apply hP
    apply GenericFiberDivisorZero.BundleCycles.ord_pullback_zero_over_generic (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S)
      (Integral.FiberFieldNaturality.BundleCycles.integralFiberProjection_genericPoint (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S)) g hg P
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hp
  refine ⟨AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S P, ?_⟩
  exact PrimeSpectrum.ext (FlatPrimeExtension.BundleCycles.flatHeightOne_isExtended P.asIdeal hheight hp
    (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection_comap_map R S _))

theorem geometricAffinePrincipalDivisor_pullback (g : (Spec (.of R)).functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of S))
        (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S) g) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S)
        (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of R)) g) := by
  have he : Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S) =
      AffinePrimePoint.BundleCycles.geometricAffinePrimePoint R S := funext (fun p => (AffinePrimePoint.BundleCycles.geometricAffinePrimePoint_eq_fiberGeneric R S p).symm)
  ext P
  change _ = Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S)) _ P
  rw [he]
  by_cases hP : P ∈ Set.range (AffinePrimePoint.BundleCycles.geometricAffinePrimePoint R S)
  · obtain ⟨p, rfl⟩ := hP
    rw [Finsupp.mapDomain_apply_of_injective (AffinePrimePoint.BundleCycles.geometricAffinePrimePoint_injective R S),
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply,
      geometricAffineProjection_order]
  · have hz : (Spec (.of S)).ord
        (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S) g) P = 0 := by
      by_contra hn
      exact hP (geometricAffinePulledDivisor_support R S g hg P hn)
    rw [Finsupp.mapDomain_of_notMem_range _ _ hP, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, hz, Int.cast_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.AffineDivisorPullback.BundleCycles
