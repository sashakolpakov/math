import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.PointSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.PrincipalDivisor

/-! # Support Dimension Drop -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.SupportDimensionDrop.BundleCycles

noncomputable section

/-! Proper pushforward kills the entire principal divisor when the actual
integral support loses dimension, including singular supports. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [X.IsSeparated] [Y.IsSeparated] (f : X ⟶ Y) [IsProper f]
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY] (x : X)

omit [AlgebraicGeometry.IsNoetherian Y] [X.IsSeparated] [Y.IsSeparated] in
theorem properPointSupport_dimension_le :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) gY ≤
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY) := by
  have h := Cycles.Functoriality.FunctionFields.Construction.dimension_le_of_genericPoint (Point.SupportMap.BundleCycles.pointSupportMap f x)
    (Point.SupportNaturality.BundleCycles.pointSupportMap_genericPoint f x _ (Point.SupportMap.BundleCycles.pointSupportMap_inclusion f x))
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (irreducibleSetEquivPoints.symm (f x)) gY)
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) gY ≤
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Point.SupportMap.BundleCycles.pointSupportMap f x ≫ CycleClass.Geometric.GenericPoint.reducedSupportι _ ≫ gY) at h
  rw [← Category.assoc, Point.SupportMap.BundleCycles.pointSupportMap_inclusion, Category.assoc] at h
  exact h

omit [AlgebraicGeometry.IsNoetherian Y] in
theorem properPushforward_principalPointSupport_of_dimension_drop
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) gY <
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY))
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField) (hg : g ≠ 0) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x) g) = 0 := by
  let a := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)
  let b := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x))
  let r := Point.SupportMap.BundleCycles.pointSupportMap f x
  let : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from a]
    infer_instance⟩
  let : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (f x))).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from b]
    infer_instance⟩
  have he : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (r ≫ (b ≫ gY)) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY) := by
    change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Point.SupportMap.BundleCycles.pointSupportMap f x ≫ CycleClass.Geometric.GenericPoint.reducedSupportι _ ≫ gY) = _
    rw [← Category.assoc, Point.SupportMap.BundleCycles.pointSupportMap_inclusion, Category.assoc]
    rfl
  have hz : IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward r (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor _ g) = 0 := by
    by_cases hc : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) gY + 1 =
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY)
    · exact Relative.PrincipalDivisor.BundleCycles.RelativePrincipalDivisor.pushforward_eq_zero r
        (Point.SupportNaturality.BundleCycles.pointSupportMap_genericPoint f x r (Point.SupportMap.BundleCycles.pointSupportMap_inclusion f x)) (b ≫ gY)
        (hc.trans he.symm) g hg
    · apply Principal.PushforwardDimensionDrop.BundleCycles.principalDivisor_pushforward_dimension_drop r (b ≫ gY) _ g
      change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) gY + 1 < _
      rw [he]
      omega
  change IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Finsupp.embDomain ⟨a, a.isClosedEmbedding.injective⟩
    (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor _ g)) = 0
  rw [Finsupp.embDomain_eq_mapDomain]
  change IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Finsupp.mapDomain a _) = 0
  exact (LineBundle.FiniteSupportProjection.Cycles.pointPushforward_supportSquare f x _).trans
    ((congrArg (Finsupp.mapDomain b) hz).trans Finsupp.mapDomain_zero)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.SupportDimensionDrop.BundleCycles
