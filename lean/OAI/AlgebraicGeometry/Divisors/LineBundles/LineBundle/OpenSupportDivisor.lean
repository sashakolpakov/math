import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenSupportPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Intersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportPointCycle

/-! # Open Support Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenSupportDivisor.Cycles

noncomputable section

/-! # LineBundleCycles: the actual divisor on an open-restricted closed support gives the restricted Chow class -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (i : X ⟶ Y) [IsOpenImmersion i] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem lineBundleDivisorOnSupport_open_class (d : ℕ) (W : IrreducibleCloseds Y)
    [Nonempty (Open.SupportRestriction.BundleCycles.openSupportPullback i W)] (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ (i ≫ f) d (Intersection.Cycles.lineBundleDivisorOnSupport (L.pullback i) (Open.SupportRestriction.BundleCycles.openRestrictedSupport i W)) =
      Open.ChowRestriction.BundleCycles.openChowRestriction i f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundleDivisorOnSupport L W)) := by
  have he : Open.SupportRestriction.BundleCycles.openRestrictedSupportMap i W ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap W f =
      CycleClass.Geometric.GenericPoint.reducedSupportι (Open.SupportRestriction.BundleCycles.openRestrictedSupport i W) ≫ (i ≫ f) := by
    change Open.SupportRestriction.BundleCycles.openRestrictedSupportMap i W ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f = _
    rw [← Category.assoc, Open.SupportRestriction.BundleCycles.openRestrictedSupportMap_inclusion, Category.assoc]
  have H := OpenCycle.Cycles.lineBundleOpen_pointCycle (Open.SupportRestriction.BundleCycles.openRestrictedSupportMap i W)
    (L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι W)) ((L.pullback i).pullback (CycleClass.Geometric.GenericPoint.reducedSupportι (Open.SupportRestriction.BundleCycles.openRestrictedSupport i W)))
    (OpenSupportPullback.Cycles.lineBundleOpenSupportPullbackIso i L W).symm (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f)
    (CycleClass.Geometric.GenericPoint.reducedSupportι (Open.SupportRestriction.BundleCycles.openRestrictedSupport i W) ≫ (i ≫ f)) he d hW
  have H' := congrArg (Closed.ChowPushforward.BundleCycles.closedChowPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι (Open.SupportRestriction.BundleCycles.openRestrictedSupport i W)) (i ≫ f) d) H
  rw [Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass, Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass,
    ← Open.SupportPointCycle.BundleCycles.openRestrictedSupport_pointCycle i W] at H'
  rw [Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass]
  exact H'

theorem lineBundleDivisorOnSupport_open_empty (d : ℕ) (W : IrreducibleCloseds Y)
    [IsEmpty (Open.SupportRestriction.BundleCycles.openSupportPullback i W)] :
    Open.ChowRestriction.BundleCycles.openChowRestriction i f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundleDivisorOnSupport L W)) = 0 := by
  rw [Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass]
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (i ≫ f) d
    (Finsupp.comapDomain i (Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W)
      (L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι W)).rationalSectionPointCycle) i.isOpenEmbedding.injective.injOn) = 0
  rw [Open.SupportPointCycle.BundleCycles.openRestrictedSupport_pointCycle_empty, map_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenSupportDivisor.Cycles
