import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.DivisorNorm
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PointSupport

/-! # Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Divisor.BundleCycles

noncomputable section

/-!
# LineBundleCycles: principal relations on actual supports under finite pushforward
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y] (i : X ⟶ Y) [IsFinite i]

def finitePointSupportNorm (x : X) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField →*
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (i x))).functionField := by
  let := (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap i x).hom.toAlgebra
  exact Algebra.norm (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (i x))).functionField

omit [AlgebraicGeometry.IsNoetherian Y] in
theorem finitePointSupportNorm_ne_zero (x : X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField) (hg : g ≠ 0) :
    finitePointSupportNorm i x g ≠ 0 := by
  let := (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap i x).hom.toAlgebra
  let : Module.Finite
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (i x))).functionField
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField :=
    LineBundles.Finite.FunctionFields.BundleCycles.finiteMorphism_functionField_finite (Point.SupportMap.BundleCycles.pointSupportMap i x)
      (Point.SupportNaturality.BundleCycles.pointSupportMap_genericPoint i x (Point.SupportMap.BundleCycles.pointSupportMap i x) (Point.SupportMap.BundleCycles.pointSupportMap_inclusion i x))
  change Algebra.norm (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (i x))).functionField g ≠ 0
  exact Algebra.norm_ne_zero_iff.mpr hg

theorem finitePushforward_principalPointSupport (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (x : X) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField)
    (hg : g ≠ 0) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x) g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (i x)) (finitePointSupportNorm i x g) := by
  let a := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)
  let b := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x))
  let r := Point.SupportMap.BundleCycles.pointSupportMap i x
  have hn := LineBundles.Finite.DivisorNorm.BundleCycles.FiniteDivisorNorm.principalDivisor_norm r
    (Point.SupportNaturality.BundleCycles.pointSupportMap_genericPoint i x r (Point.SupportMap.BundleCycles.pointSupportMap_inclusion i x))
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (irreducibleSetEquivPoints.symm (i x)) f) g hg
  change IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i (Finsupp.embDomain ⟨a, a.isClosedEmbedding.injective⟩
    (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor _ g)) =
      Finsupp.embDomain ⟨b, b.isClosedEmbedding.injective⟩
        (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor _ (finitePointSupportNorm i x g))
  rw [Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain]
  change IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i (Finsupp.mapDomain a _) = Finsupp.mapDomain b _
  rw [← IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion a, ← IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion b,
    ← LinearMap.comp_apply, ← IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, ← Point.SupportMap.BundleCycles.pointSupportMap_inclusion i x,
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, LinearMap.comp_apply]
  exact congrArg (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward b) hn

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Divisor.BundleCycles
