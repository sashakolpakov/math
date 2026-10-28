import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpaceChartBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.DivisorPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorOpenRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian

/-! # Locally Affine Space Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyAffineSpaceDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: global rational principal-divisor pullback for actual affine-space bundles -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem locallyAffineSpacePrincipalDivisor_pullback {E X : Scheme.{0}}
    [IsIntegral E] [IsIntegral X] [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] (p : E ⟶ X) [GeometricallyIntegral p]
    (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p) (g : X.functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor E (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) := by
  ext z
  obtain ⟨U, i, ι, hι, j, hi, hj, hx, hs⟩ := h (p z)
  let := hι
  let := hi
  let := hj
  obtain ⟨u, hu⟩ := hx
  have : Nonempty U := ⟨u⟩
  have : IsIntegral U := isIntegral_of_isOpenImmersion i
  have : AlgebraicGeometry.IsNoetherian U := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian i
  obtain ⟨a, ha, hja⟩ := Scheme.exists_preimage_of_isPullback hs u z hu
  have hfield : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap j (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g) =
      Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace ι U ↘ U) (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i g) :=
    ConcreteCategory.congr_hom
      (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap_openSquare p (AffineSpace ι U ↘ U) i j hs.w.symm) g
  have hg' : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i g ≠ 0 :=
    (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i).hom.injective).mpr hg
  have hlocal :
      Finsupp.comapDomain j (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor E (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g))
          j.isOpenEmbedding.injective.injOn =
        Finsupp.comapDomain j (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g))
          j.isOpenEmbedding.injective.injOn := by
    rw [Principal.DivisorOpenRestriction.BundleCycles.rationalPrincipalPointDivisor_openRestriction, hfield,
      LineBundles.AffineSpace.DivisorPullback.BundleCycles.affineSpacePrincipalDivisor_pullback U ι _ hg',
      Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_openRestriction p (AffineSpace ι U ↘ U) i j hs,
      Principal.DivisorOpenRestriction.BundleCycles.rationalPrincipalPointDivisor_openRestriction]
  have hcoeff := congrArg (fun w : AffineSpace ι U →₀ ℚ => w a) hlocal
  change RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor E (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g) (j a) =
    Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) (j a) at hcoeff
  simpa only [hja] using hcoeff

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyAffineSpaceDivisor.BundleCycles
