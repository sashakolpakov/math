import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FiniteChowProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IsoDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Intersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportRegularFunction

/-! # Finite Support Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FiniteSupportProjection.Cycles

noncomputable section

/-! # LineBundleCycles: finite projection of line-bundle intersection classes on arbitrary actual integral supports -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (f : X ⟶ Y) (x : X)

def lineBundlePointSupportPullbackIso (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y) :
    ((L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x)))).pullback (Point.SupportMap.BundleCycles.pointSupportMap f x)).sheaf ≅
      ((L.pullback f).pullback (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x))).sheaf :=
  Module.PullbackSquareSections.BundleCycles.modulePullbackSquareIso (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x))) (Point.SupportMap.BundleCycles.pointSupportMap f x)
    f (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) (Point.SupportMap.BundleCycles.pointSupportMap_inclusion f x) L.sheaf

theorem pointPushforward_supportSquare (z : CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x) →₀ ℚ) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) z) =
      Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x))) (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (Point.SupportMap.BundleCycles.pointSupportMap f x) z) := by
  rw [← IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)),
    ← IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x))),
    ← LinearMap.comp_apply, ← IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, ← Point.SupportMap.BundleCycles.pointSupportMap_inclusion f x,
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, LinearMap.comp_apply]

variable [AlgebraicGeometry.IsNoetherian Y] [IsFinite f]
    (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType g] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)
    (d : ℕ) (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) g = d + 1)

include hd in
theorem lineBundleDivisorOnSupport_finite_projection :
    Point.CycleChow.BundleCycles.pointCycleToChowQ g d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Intersection.Cycles.lineBundleDivisorOnSupport (L.pullback f) (irreducibleSetEquivPoints.symm x))) =
      (f.residueDegree x : ℚ) • Point.CycleChow.BundleCycles.pointCycleToChowQ g d
        (Intersection.Cycles.lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm (f x))) := by
  let jX := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)
  let jY := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x))
  let r := Point.SupportMap.BundleCycles.pointSupportMap f x
  let M := L.pullback jY
  let N := (L.pullback f).pullback jX
  let hη := Point.SupportNaturality.BundleCycles.pointSupportMap_genericPoint f x r (Point.SupportMap.BundleCycles.pointSupportMap_inclusion f x)
  have hdX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (r ≫ (jY ≫ g)) = d + 1 :=
    (Finite.PointSupport.BundleCycles.schemeDimension_eq_of_finite r hη (jY ≫ g)).symm.trans hd
  have hi := IsoDivisor.Cycles.lineBundleIso_chowClass (L := M.pullback r) (M := N)
    (lineBundlePointSupportPullbackIso f x L) (r ≫ (jY ≫ g)) d hdX
  have hf := FiniteChowProjection.Cycles.finiteChowPushforward_lineBundleClass r hη (jY ≫ g) M d hd
  have h := congrArg (Finite.ChowPushforward.BundleCycles.finiteChowPushforward jY g d)
    ((congrArg (Finite.ChowPushforward.BundleCycles.finiteChowPushforward r (jY ≫ g) d) hi.symm).trans hf)
  change Finite.ChowPushforward.BundleCycles.finiteChowPushforward jY g d
      (Finite.ChowPushforward.BundleCycles.finiteChowPushforward r (jY ≫ g) d (Point.CycleChow.BundleCycles.pointCycleToChowQ (r ≫ (jY ≫ g)) d N.rationalSectionPointCycle)) =
    Finite.ChowPushforward.BundleCycles.finiteChowPushforward jY g d ((r.residueDegree (genericPoint _) : ℚ) •
      Point.CycleChow.BundleCycles.pointCycleToChowQ (jY ≫ g) d M.rationalSectionPointCycle) at h
  rw [Finite.ChowPointClass.BundleCycles.finiteChowPushforward_pointClass, Finite.ChowPointClass.BundleCycles.finiteChowPushforward_pointClass,
    map_smul, Finite.ChowPointClass.BundleCycles.finiteChowPushforward_pointClass, Point.SupportRegularFunction.BundleCycles.pointSupportMap_residueDegree f x,
    IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion jY,
    IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion jY] at h
  change Point.CycleChow.BundleCycles.pointCycleToChowQ g d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Finsupp.mapDomain jX N.rationalSectionPointCycle)) = _
  exact (congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ g d) (pointPushforward_supportSquare f x N.rationalSectionPointCycle)).trans h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FiniteSupportProjection.Cycles
