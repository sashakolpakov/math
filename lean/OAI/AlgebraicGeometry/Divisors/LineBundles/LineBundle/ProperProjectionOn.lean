import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperGlobalProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowNe
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FiniteSupportProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Intersection

/-! # Proper Projection On -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperProjectionOn.Cycles

noncomputable section

section

/-! # LineBundleCycles: proper projection of actual pulled line-bundle divisor classes with the genuine generic degree -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [X.IsSeparated] [Y.IsSeparated]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)
    (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY) = d + 1)

include hd hη in
theorem properChowPushforward_lineBundleClass :
    Proper.ChowNe.BundleCycles.properChowPushforward f gY d ((L.pullback f).rationalSectionChowClass (f ≫ gY) d) =
      (f.residueDegree (genericPoint X) : ℚ) • L.rationalSectionChowClass gY d := by
  let b := L.dominantPullbackSectionCoefficient f hη 1
  have hs := (L.pullback f).rationalSectionChowClass_coefficient_independent (f ≫ gY) d hd b
  have h1 : RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y (1 : Y.functionField) = 0 := by
    change (Ord.BundleCycles.principalDivisor Y (1 : Y.functionField)).mapRange _ _ = 0
    rw [Principal.DivisorLaws.BundleCycles.principalDivisor_one, Finsupp.mapRange_zero]
  have ht : Point.CycleChow.BundleCycles.pointCycleToChowQ gY d (L.rationalSectionPointCycleWithCoefficient 1) =
      L.rationalSectionChowClass gY d := by
    rw [LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointCycleWithCoefficient_eq]
    change Point.CycleChow.BundleCycles.pointCycleToChowQ gY d (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y 1 + L.rationalSectionPointCycle) = _
    rw [h1, zero_add]
    rfl
  have hp := congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ gY d) (ProperGlobalProjection.Cycles.properPushforward_lineBundleSection f hη gY L 1)
  rw [map_smul] at hp
  calc
    _ = Proper.ChowNe.BundleCycles.properChowPushforward f gY d
        (Point.CycleChow.BundleCycles.pointCycleToChowQ (f ≫ gY) d ((L.pullback f).rationalSectionPointCycleWithCoefficient b)) :=
      congrArg (Proper.ChowNe.BundleCycles.properChowPushforward f gY d) hs.symm
    _ = Point.CycleChow.BundleCycles.pointCycleToChowQ gY d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f
        ((L.pullback f).rationalSectionPointCycleWithCoefficient b)) :=
      Proper.ChowNe.BundleCycles.properChowPushforward_pointClass f gY d _
    _ = (f.residueDegree (genericPoint X) : ℚ) • Point.CycleChow.BundleCycles.pointCycleToChowQ gY d
        (L.rationalSectionPointCycleWithCoefficient 1) := hp
    _ = _ := congrArg (fun z => (f.residueDegree (genericPoint X) : ℚ) • z) ht

end

section

/-! Proper projection for actual line-bundle intersection classes on integral supports. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [X.IsSeparated] [Y.IsSeparated] (f : X ⟶ Y) (x : X)

variable [AlgebraicGeometry.IsNoetherian Y] [IsProper f]
    (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType g] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)
    (d : ℕ) (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ g) = d + 1)

include hd in
theorem lineBundleDivisorOnSupport_proper_projection :
    Point.CycleChow.BundleCycles.pointCycleToChowQ g d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Intersection.Cycles.lineBundleDivisorOnSupport (L.pullback f) (irreducibleSetEquivPoints.symm x))) =
      (f.residueDegree x : ℚ) • Point.CycleChow.BundleCycles.pointCycleToChowQ g d
        (Intersection.Cycles.lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm (f x))) := by
  let jX := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)
  let jY := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x))
  let r := Point.SupportMap.BundleCycles.pointSupportMap f x
  let M := L.pullback jY
  let N := (L.pullback f).pullback jX
  let hη := Point.SupportNaturality.BundleCycles.pointSupportMap_genericPoint f x r (Point.SupportMap.BundleCycles.pointSupportMap_inclusion f x)
  let : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from jX]
    infer_instance⟩
  let : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (f x))).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from jY]
    infer_instance⟩
  have hdX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (r ≫ (jY ≫ g)) = d + 1 := by
    change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Point.SupportMap.BundleCycles.pointSupportMap f x ≫ CycleClass.Geometric.GenericPoint.reducedSupportι _ ≫ g) = _
    rw [← Category.assoc, Point.SupportMap.BundleCycles.pointSupportMap_inclusion, Category.assoc]
    exact hd
  have hi := IsoDivisor.Cycles.lineBundleIso_chowClass (L := M.pullback r) (M := N)
    (FiniteSupportProjection.Cycles.lineBundlePointSupportPullbackIso f x L) (r ≫ (jY ≫ g)) d hdX
  have hf := properChowPushforward_lineBundleClass r hη (jY ≫ g) M d hdX
  have h := congrArg (Proper.ChowNe.BundleCycles.properChowPushforward jY g d)
    ((congrArg (Proper.ChowNe.BundleCycles.properChowPushforward r (jY ≫ g) d) hi.symm).trans hf)
  change Proper.ChowNe.BundleCycles.properChowPushforward jY g d
      (Proper.ChowNe.BundleCycles.properChowPushforward r (jY ≫ g) d (Point.CycleChow.BundleCycles.pointCycleToChowQ (r ≫ (jY ≫ g)) d N.rationalSectionPointCycle)) =
    Proper.ChowNe.BundleCycles.properChowPushforward jY g d ((r.residueDegree (genericPoint _) : ℚ) •
      Point.CycleChow.BundleCycles.pointCycleToChowQ (jY ≫ g) d M.rationalSectionPointCycle) at h
  rw [Proper.ChowNe.BundleCycles.properChowPushforward_pointClass, Proper.ChowNe.BundleCycles.properChowPushforward_pointClass,
    map_smul, Proper.ChowNe.BundleCycles.properChowPushforward_pointClass, Point.SupportRegularFunction.BundleCycles.pointSupportMap_residueDegree f x,
    IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion jY,
    IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion jY] at h
  change Point.CycleChow.BundleCycles.pointCycleToChowQ g d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Finsupp.mapDomain jX N.rationalSectionPointCycle)) = _
  exact (congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ g d) (FiniteSupportProjection.Cycles.pointPushforward_supportSquare f x N.rationalSectionPointCycle)).trans h

end

/-! # LineBundleCycles: proper projection for the complete point cycle of a fixed dimension -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [X.IsSeparated] [Y.IsSeparated]
    (f : X ⟶ Y) [IsProper f] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType g]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)

theorem lineBundlePointIntersection_proper_projection (d : ℕ) (z : X →₀ ℚ)
    (hz : ∀ x, z x ≠ 0 → Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ g) = d + 1) :
    Proper.ChowNe.BundleCycles.properChowPushforward f g d (Point.CycleChow.BundleCycles.pointCycleToChowQ (f ≫ g) d (Intersection.Cycles.lineBundlePointIntersection (L.pullback f) z)) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ g d (Intersection.Cycles.lineBundlePointIntersection L (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f z)) := by
  let A := (Proper.ChowNe.BundleCycles.properChowPushforward f g d).comp
    ((Point.CycleChow.BundleCycles.pointCycleToChowQ (f ≫ g) d).comp (Intersection.Cycles.lineBundlePointIntersection (L.pullback f)))
  let B := (Point.CycleChow.BundleCycles.pointCycleToChowQ g d).comp ((Intersection.Cycles.lineBundlePointIntersection L).comp (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f))
  change A z = B z
  rw [← z.sum_single, map_finsuppSum, map_finsuppSum]
  apply Finset.sum_congr rfl
  intro x hx
  change Proper.ChowNe.BundleCycles.properChowPushforward f g d
      (Point.CycleChow.BundleCycles.pointCycleToChowQ (f ≫ g) d (Intersection.Cycles.lineBundlePointIntersection (L.pullback f) (Finsupp.single x (z x)))) =
    Point.CycleChow.BundleCycles.pointCycleToChowQ g d (Intersection.Cycles.lineBundlePointIntersection L (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Finsupp.single x (z x))))
  rw [Intersection.Cycles.lineBundlePointIntersection_single, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single, Intersection.Cycles.lineBundlePointIntersection_single,
    map_smul, map_smul, map_smul, Proper.ChowNe.BundleCycles.properChowPushforward_pointClass,
    lineBundleDivisorOnSupport_proper_projection f x g L d
      (hz x (Finsupp.mem_support_iff.mp hx)), smul_smul]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperProjectionOn.Cycles
