import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleSet
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CyclePartition
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowPointClass

/-! # Clopen Point Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ClopenPointChow.BundleCycles

noncomputable section

/-! Selecting a clopen part of a point cycle is the composite of the
actual open restriction and closed Chow pushforward. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem pointCycleSetPart_range {X U : Type} (i : U → X) (hi : Function.Injective i) (z : X →₀ ℚ) :
    Point.CycleSet.BundleCycles.pointCycleSetPart (Set.range i) z = Finsupp.mapDomain i (Finsupp.comapDomain i z hi.injOn) := by
  ext x
  by_cases hx : x ∈ Set.range i
  · exact (Point.CycleSet.BundleCycles.pointCycleSetPart_apply_mem _ _ x hx).trans (Point.CyclePartition.BundleCycles.pointCycle_map_comap_apply_of_mem i hi z x hx).symm
  · exact (Point.CycleSet.BundleCycles.pointCycleSetPart_apply_notMem _ _ x hx).trans (Finsupp.mapDomain_of_notMem_range _ _ hx).symm

variable {U X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian U] [AlgebraicGeometry.IsNoetherian X]
    (i : U ⟶ X) [IsOpenImmersion i] [IsClosedImmersion i]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d : ℕ)

def clopenChowPart : DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d :=
  (Closed.ChowPushforward.BundleCycles.closedChowPushforward i f d).comp (Open.ChowRestriction.BundleCycles.openChowRestriction i f d)

theorem clopenChowPart_pointClass (z : X →₀ ℚ) :
    clopenChowPart i f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Point.CycleSet.BundleCycles.pointCycleSetPart (Set.range i) z) := by
  change Closed.ChowPushforward.BundleCycles.closedChowPushforward i f d (Open.ChowRestriction.BundleCycles.openChowRestriction i f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z)) = _
  rw [Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass, Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass,
    pointCycleSetPart_range i i.isOpenEmbedding.injective]

theorem clopenPointChowPart_eq_of_eq (z w : X →₀ ℚ)
    (hzw : Point.CycleChow.BundleCycles.pointCycleToChowQ f d z = Point.CycleChow.BundleCycles.pointCycleToChowQ f d w) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Point.CycleSet.BundleCycles.pointCycleSetPart (Set.range i) z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Point.CycleSet.BundleCycles.pointCycleSetPart (Set.range i) w) := by
  rw [← clopenChowPart_pointClass i f d, hzw, clopenChowPart_pointClass]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ClopenPointChow.BundleCycles
