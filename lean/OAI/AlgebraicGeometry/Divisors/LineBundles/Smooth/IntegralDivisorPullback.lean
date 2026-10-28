import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralAffineSourceCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.AffineSchemeDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian

/-! # Integral Divisor Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralDivisorPullback.BundleCycles

noncomputable section

/-! Rational principal divisors pull back along arbitrary smooth morphisms
with geometrically integral fibers, by the actual affine source charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem smoothIntegralPrincipalDivisor_pullback {E X : Scheme.{0}}
    [IsIntegral E] [IsIntegral X] [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (g : X.functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor E (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) := by
  ext z
  obtain ⟨U, V, q, i, j, hU, hV, hq, hgi, hi, hj, hz, hs⟩ :=
    IntegralAffineSourceCharts.BundleCycles.smoothIntegral_hasAffineSourceCharts p z
  let := hU
  let := hV
  let := hq
  let := hgi
  let := hi
  let := hj
  obtain ⟨a, hja⟩ := hz
  let : Nonempty V := ⟨a⟩
  let : Nonempty U := ⟨q a⟩
  let : IsIntegral U := isIntegral_of_isOpenImmersion i
  let : IsIntegral V := isIntegral_of_isOpenImmersion j
  let : AlgebraicGeometry.IsNoetherian U := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian i
  let : AlgebraicGeometry.IsNoetherian V := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian j
  have hfield : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap j (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g) =
      Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap q (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i g) :=
    ConcreteCategory.congr_hom (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap_openSquare p q i j hs.symm) g
  have hg' : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i g ≠ 0 :=
    (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i).hom.injective).mpr hg
  have hlocal :
      Finsupp.comapDomain j (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor E (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g))
          j.isOpenEmbedding.injective.injOn =
        Finsupp.comapDomain j (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g))
          j.isOpenEmbedding.injective.injOn := by
    rw [Principal.DivisorOpenRestriction.BundleCycles.rationalPrincipalPointDivisor_openRestriction, hfield,
      AffineSchemeDivisor.BundleCycles.smoothAffineSchemePrincipalDivisor_pullback q _ hg',
      Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_openSquare p q i j hs,
      Principal.DivisorOpenRestriction.BundleCycles.rationalPrincipalPointDivisor_openRestriction]
  have hcoeff := congrArg (fun w : V →₀ ℚ => w a) hlocal
  change RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor E (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g) (j a) =
    Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) (j a) at hcoeff
  simpa only [hja] using hcoeff

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralDivisorPullback.BundleCycles
