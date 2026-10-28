import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.GradedPointPreimage
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleDimensionDecomposition

/-! # Point Preimage -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.PointPreimage.Cycles

noncomputable section

/-! Every finite point cycle on a constant-rank affine-space bundle has a
finite point-cycle preimage, with equality in every dimension-graded Chow group. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineBundlePointChow_preimage_of_rank {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (h : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r)
    (β : E →₀ ℚ) : ∃ z : X →₀ ℚ, ∀ d : ℕ,
      Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) = Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d β := by
  classical
  let ι := {e // e ∈ Point.CycleDimensionDecomposition.BundleCycles.pointCycleDimensionGrades (p ≫ f) β}
  have H : ∀ e : ι, ∃ z : X →₀ ℚ, ∀ d : ℕ,
      Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) =
        Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d
          (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (p ≫ f) e.val (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (p ≫ f) e.val β)) :=
    fun e => GradedPointPreimage.Cycles.affineBundle_gradedCycle_pointPreimage p f r h e.val _
  choose z hz using H
  refine ⟨∑ e : ι, z e, ?_⟩
  intro d
  rw [map_sum, map_sum]
  calc
    _ = ∑ e : ι, Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d
        (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (p ≫ f) e.val (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (p ≫ f) e.val β)) :=
      Finset.sum_congr rfl (fun e _ => hz e d)
    _ = Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d β := by
      rw [← map_sum, Point.CycleDimensionDecomposition.BundleCycles.pointCycle_dimension_decomposition]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.PointPreimage.Cycles
