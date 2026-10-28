import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.FiberPushforward

/-! # Closed Fiber Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ClosedFiberClass.BundleCycles

noncomputable section

/-! # LineBundleCycles: finite pushforward preserves a zero class on the actual closed fiber -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y Z : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Z]
    (i : X ⟶ Y) [IsFinite i] (j : Z ⟶ Y) [IsClosedImmersion j]
    [AlgebraicGeometry.IsNoetherian (pullback i j)]
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem finiteClosedFiber_class_zero (d : ℕ) (z : X →₀ ℚ)
    (hz : Point.CycleChow.BundleCycles.closedPointCycleToChowQ (pullback.fst i j) (i ≫ f) d z = 0) :
    Point.CycleChow.BundleCycles.closedPointCycleToChowQ j f d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i z) = 0 := by
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (pullback.fst i j ≫ i ≫ f) d
    (Finsupp.comapDomain (pullback.fst i j) z (pullback.fst i j).isClosedEmbedding.injective.injOn) = 0 at hz
  have hmap : pullback.fst i j ≫ i ≫ f = pullback.snd i j ≫ j ≫ f := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
  rw [hmap] at hz
  have hc := congrArg (ChowPushforward.BundleCycles.finiteChowPushforward (pullback.snd i j) (j ≫ f) d) hz
  rw [map_zero, ChowPointClass.BundleCycles.finiteChowPushforward_pointClass, Closed.FiberPushforward.BundleCycles.pullbackClosed_pointPushforward] at hc
  exact hc

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ClosedFiberClass.BundleCycles
