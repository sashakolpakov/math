import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralDivisorPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport

/-! # Integral Principal Relations -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralPrincipalRelations.BundleCycles

noncomputable section

/-! Smooth morphisms with geometrically integral fibers preserve every
principal-divisor relation, including those on singular closed supports. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem smoothIntegralCycleExtension_principal {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
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
        (IntegralDivisorPullback.BundleCycles.smoothIntegralPrincipalDivisor_pullback q g hg).symm).trans
        (Integral.ClosedImage.BundleCycles.integralClosedImage_principalDivisor j _)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralPrincipalRelations.BundleCycles
