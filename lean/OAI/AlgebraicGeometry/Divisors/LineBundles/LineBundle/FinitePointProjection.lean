import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FiniteSupportProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Intersection

/-! # Finite Point Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FinitePointProjection.Cycles

noncomputable section

/-! # LineBundleCycles: finite projection for the complete point cycle of a fixed dimension -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType g]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)

theorem lineBundlePointIntersection_finite_projection (d : ℕ) (z : X →₀ ℚ)
    (hz : ∀ x, z x ≠ 0 → Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ g) = d + 1) :
    Finite.ChowPushforward.BundleCycles.finiteChowPushforward f g d (Point.CycleChow.BundleCycles.pointCycleToChowQ (f ≫ g) d (Intersection.Cycles.lineBundlePointIntersection (L.pullback f) z)) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ g d (Intersection.Cycles.lineBundlePointIntersection L (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f z)) := by
  let A := (Finite.ChowPushforward.BundleCycles.finiteChowPushforward f g d).comp
    ((Point.CycleChow.BundleCycles.pointCycleToChowQ (f ≫ g) d).comp (Intersection.Cycles.lineBundlePointIntersection (L.pullback f)))
  let B := (Point.CycleChow.BundleCycles.pointCycleToChowQ g d).comp ((Intersection.Cycles.lineBundlePointIntersection L).comp (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f))
  change A z = B z
  rw [← z.sum_single, map_finsuppSum, map_finsuppSum]
  apply Finset.sum_congr rfl
  intro x hx
  change Finite.ChowPushforward.BundleCycles.finiteChowPushforward f g d
      (Point.CycleChow.BundleCycles.pointCycleToChowQ (f ≫ g) d (Intersection.Cycles.lineBundlePointIntersection (L.pullback f) (Finsupp.single x (z x)))) =
    Point.CycleChow.BundleCycles.pointCycleToChowQ g d (Intersection.Cycles.lineBundlePointIntersection L (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Finsupp.single x (z x))))
  rw [Intersection.Cycles.lineBundlePointIntersection_single, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single, Intersection.Cycles.lineBundlePointIntersection_single,
    map_smul, map_smul, map_smul, Finite.ChowPointClass.BundleCycles.finiteChowPushforward_pointClass,
    FiniteSupportProjection.Cycles.lineBundleDivisorOnSupport_finite_projection f x g L d
      ((Finite.PointSupport.BundleCycles.pointClosure_dimension_finite f g x).trans (hz x (Finsupp.mem_support_iff.mp hx))), smul_smul]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FinitePointProjection.Cycles
