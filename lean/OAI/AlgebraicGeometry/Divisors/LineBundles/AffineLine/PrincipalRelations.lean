import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Support
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.DivisorPullback

/-! # Principal Relations -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PrincipalRelations.BundleCycles

noncomputable section

/-! # LineBundleCycles: all actual principal-divisor relations pull back to the relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]

theorem affineLineCycleExtension_principal (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (Support.BundleCycles.affineLineExtendedSupport X W) (Support.BundleCycles.affineLineExtendedFunction X W g) := by
  let A := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let j := Support.BundleCycles.affineLineSupportMap X W
  have he : Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g :=
    (Finsupp.embDomain_eq_mapDomain
      ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g)).symm
  have hnat := Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_naturality (Charts.BundleCycles.affineLineProjection X) (Charts.BundleCycles.affineLineProjection A)
    (CycleClass.Geometric.GenericPoint.reducedSupportι W) j (Support.BundleCycles.affineLineSupport_isPullback X W) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g)
  exact (congrArg (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X)) he.symm).trans
    (hnat.symm.trans
      ((congrArg (Finsupp.mapDomain j) (DivisorPullback.BundleCycles.affineLinePrincipalDivisor_pullback A g hg).symm).trans
        (Integral.ClosedImage.BundleCycles.integralClosedImage_principalDivisor j _)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PrincipalRelations.BundleCycles
