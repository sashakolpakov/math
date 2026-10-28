import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceBase
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.DivisorPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorOpenRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian

/-! # Source Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: principal-divisor pullback from relative affine-space charts covering the source -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineSpaceSourcePrincipalDivisor_pullback {E X : Scheme.{0}}
    [IsIntegral E] [IsIntegral X] [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] (p : E ⟶ X) [GeometricallyIntegral p]
    (h : SourceBase.BundleCycles.HasAffineSpaceSourceCharts p) (g : X.functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor E (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) := by
  ext z
  obtain ⟨U, i, ι, hι, j, hi, hj, hx, hs⟩ := h z
  let := hι
  let := hi
  let := hj
  obtain ⟨a, hja⟩ := hx
  have : Nonempty U := ⟨(AffineSpace ι U ↘ U) a⟩
  have : IsIntegral U := isIntegral_of_isOpenImmersion i
  have : AlgebraicGeometry.IsNoetherian U := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian i
  have hfield : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap j (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g) =
      Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (AffineSpace ι U ↘ U) (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i g) :=
    ConcreteCategory.congr_hom
      (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap_openSquare p (AffineSpace ι U ↘ U) i j hs.symm) g
  have hg' : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i g ≠ 0 :=
    (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i).hom.injective).mpr hg
  have hlocal :
      Finsupp.comapDomain j (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor E (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g))
          j.isOpenEmbedding.injective.injOn =
        Finsupp.comapDomain j (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g))
          j.isOpenEmbedding.injective.injOn := by
    rw [Principal.DivisorOpenRestriction.BundleCycles.rationalPrincipalPointDivisor_openRestriction, hfield,
      DivisorPullback.BundleCycles.affineSpacePrincipalDivisor_pullback U ι _ hg',
      Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_openSquare p (AffineSpace ι U ↘ U) i j hs,
      Principal.DivisorOpenRestriction.BundleCycles.rationalPrincipalPointDivisor_openRestriction]
  have hcoeff := congrArg (fun w : AffineSpace ι U →₀ ℚ => w a) hlocal
  change RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor E (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g) (j a) =
    Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) (j a) at hcoeff
  simpa only [hja] using hcoeff

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceDivisor.BundleCycles
