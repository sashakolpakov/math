import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.DivisorNorm
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FiniteSupportProjection

/-! # Point Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.PointSupport.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual proper support maps and the norm formula on supports of equal dimension -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY] (x : X)

instance properPointSupportMap_isProper : IsProper (Point.SupportMap.BundleCycles.pointSupportMap f x) := by
  let j := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x))
  let : IsProper (Point.SupportMap.BundleCycles.pointSupportMap f x ≫ j) := by
    change IsProper (Point.SupportMap.BundleCycles.pointSupportMap f x ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x)))
    rw [Point.SupportMap.BundleCycles.pointSupportMap_inclusion]
    infer_instance
  exact IsProper.of_comp (Point.SupportMap.BundleCycles.pointSupportMap f x) j

def properPointSupportNorm :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField →*
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (f x))).functionField := by
  let := (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap f x).hom.toAlgebra
  exact Algebra.norm (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (f x))).functionField

omit [AlgebraicGeometry.IsNoetherian Y] in
theorem properPointSupport_functionField_finite
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) gY =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY)) :
    letI := (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap f x).hom.toAlgebra
    Module.Finite (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (f x))).functionField
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField := by
  apply Cycles.Functoriality.FunctionFields.Construction.genericField_extension_finite (Point.SupportMap.BundleCycles.pointSupportMap f x)
    (Point.SupportNaturality.BundleCycles.pointSupportMap_genericPoint f x _ (Point.SupportMap.BundleCycles.pointSupportMap_inclusion f x))
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (irreducibleSetEquivPoints.symm (f x)) gY)
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) gY =
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Point.SupportMap.BundleCycles.pointSupportMap f x ≫ CycleClass.Geometric.GenericPoint.reducedSupportι _ ≫ gY)
  rw [← Category.assoc, Point.SupportMap.BundleCycles.pointSupportMap_inclusion, Category.assoc]
  exact hd

theorem properPushforward_principalPointSupport_of_dimension_eq
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) gY =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY))
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField) (hg : g ≠ 0) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x) g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (f x)) (properPointSupportNorm f x g) := by
  let a := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)
  let b := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x))
  let r := Point.SupportMap.BundleCycles.pointSupportMap f x
  have hn := DivisorNorm.BundleCycles.ProperDivisorNorm.principalDivisor_norm r
    (Point.SupportNaturality.BundleCycles.pointSupportMap_genericPoint f x r (Point.SupportMap.BundleCycles.pointSupportMap_inclusion f x))
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (irreducibleSetEquivPoints.symm (f x)) gY)
    (properPointSupport_functionField_finite f gY x hd) g hg
  change IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Finsupp.embDomain ⟨a, a.isClosedEmbedding.injective⟩
    (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor _ g)) =
      Finsupp.embDomain ⟨b, b.isClosedEmbedding.injective⟩
        (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor _ (properPointSupportNorm f x g))
  rw [Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain]
  change IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Finsupp.mapDomain a _) = Finsupp.mapDomain b _
  exact (LineBundle.FiniteSupportProjection.Cycles.pointPushforward_supportSquare f x _).trans (congrArg (Finsupp.mapDomain b) hn)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.PointSupport.BundleCycles
