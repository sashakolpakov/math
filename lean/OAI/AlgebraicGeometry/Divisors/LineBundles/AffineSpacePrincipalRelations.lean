import OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyAffineSpaceDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpaceBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport

/-! # Affine Space Principal Relations -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpacePrincipalRelations.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual affine-space bundles preserve every singular-support principal-divisor relation -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem locallyAffineSpaceCycleExtension_principal {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p] (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p)
    (W : IrreducibleCloseds X) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (Integral.PulledSupport.BundleCycles.integralPulledSupport p W) (Integral.PulledSupport.BundleCycles.integralPulledSupportFunction p W g) := by
  let A := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let j := Integral.PulledSupport.BundleCycles.integralPulledSupportInclusion p W
  let q := Integral.PulledSupport.BundleCycles.integralPulledSupportProjection p W
  have he : Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g :=
    (Finsupp.embDomain_eq_mapDomain
      ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g)).symm
  have hnat := Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_naturality p q (CycleClass.Geometric.GenericPoint.reducedSupportι W) j
    (Integral.PulledSupport.BundleCycles.integralPulledSupport_isPullback p W) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g)
  exact (congrArg (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p) he.symm).trans
    (hnat.symm.trans
      ((congrArg (Finsupp.mapDomain j)
        (LocallyAffineSpaceDivisor.BundleCycles.locallyAffineSpacePrincipalDivisor_pullback q
          (AffineSpaceBaseChange.BundleCycles.integralPulledSupport_hasAffineSpaceCharts p h W) g hg).symm).trans
        (Integral.ClosedImage.BundleCycles.integralClosedImage_principalDivisor j _)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpacePrincipalRelations.BundleCycles
