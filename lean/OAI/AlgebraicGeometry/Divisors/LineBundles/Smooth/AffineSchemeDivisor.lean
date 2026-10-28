import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.AffineDivisorPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorOpenRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFieldNaturality

/-! # Affine Scheme Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.AffineSchemeDivisor.BundleCycles

noncomputable section

/-! The affine divisor formula transported through the canonical spectrum
isomorphisms of the source and target schemes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem smoothAffineSchemePrincipalDivisor_pullback {E X : Scheme.{0}}
    [IsAffine E] [IsAffine X] [IsIntegral E] [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (g : X.functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor E (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) := by
  let R := Γ(X, ⊤)
  let S := Γ(E, ⊤)
  let : Algebra R S := p.appTop.hom.toAlgebra
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let : IsNoetherianRing S := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top E⟩
  let q := AlgebraSpectrumProjection.BundleCycles.algebraSpectrumProjection R S
  have hs : IsPullback q E.isoSpec.inv X.isoSpec.inv p :=
    IsPullback.of_vert_isIso ⟨Scheme.isoSpec_inv_naturality p⟩
  let : Smooth q := MorphismProperty.of_isPullback hs.flip inferInstance
  let : GeometricallyIntegral q := MorphismProperty.of_isPullback hs.flip inferInstance
  have hfield : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap E.isoSpec.inv (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g) =
      Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap q (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap X.isoSpec.inv g) :=
    ConcreteCategory.congr_hom
      (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap_openSquare p q X.isoSpec.inv E.isoSpec.inv hs.w.symm) g
  have hg' : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap X.isoSpec.inv g ≠ 0 :=
    (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap X.isoSpec.inv).hom.injective).mpr hg
  have hlocal :
      Finsupp.comapDomain E.isoSpec.inv (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor E (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap p g))
          E.isoSpec.inv.isOpenEmbedding.injective.injOn =
        Finsupp.comapDomain E.isoSpec.inv (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g))
          E.isoSpec.inv.isOpenEmbedding.injective.injOn := by
    rw [Principal.DivisorOpenRestriction.BundleCycles.rationalPrincipalPointDivisor_openRestriction, hfield,
      Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_openSquare p q X.isoSpec.inv E.isoSpec.inv hs.w,
      Principal.DivisorOpenRestriction.BundleCycles.rationalPrincipalPointDivisor_openRestriction]
    exact Geometric.AffineDivisorPullback.BundleCycles.geometricAffinePrincipalDivisor_pullback R S _ hg'
  ext z
  obtain ⟨a, rfl⟩ := E.isoSpec.inv.surjective z
  exact congrArg (fun w : Spec (.of S) →₀ ℚ => w a) hlocal

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.AffineSchemeDivisor.BundleCycles
