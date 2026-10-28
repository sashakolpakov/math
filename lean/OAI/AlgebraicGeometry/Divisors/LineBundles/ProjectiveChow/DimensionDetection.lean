import OAI.AlgebraicGeometry.Divisors.LineBundles.ChowToProjectiveChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleDimensionDecomposition

/-! # Dimension Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.DimensionDetection.BundleCycles

noncomputable section

/-! All dimension grades jointly detect the actual codimension Chow
quotient, including smooth projective schemes of mixed dimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)

theorem projectivePointChowClass_eq_zero_of_all_dimensions (z : X.carrier →₀ ℚ)
    (hz : ∀ d, Point.CycleChow.BundleCycles.pointCycleToChowQ X.structureMap d z = 0) : Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p z = 0 := by
  rw [← Point.CycleDimensionDecomposition.BundleCycles.pointCycle_dimension_decomposition X.structureMap z, map_sum]
  apply Finset.sum_eq_zero
  intro d _
  have H := congrArg (ChowToProjectiveChow.BundleCycles.dimensionChowToProjectiveChow X p d.val) (hz d.val)
  rw [map_zero, ChowToProjectiveChow.BundleCycles.dimensionChowToProjectiveChow_pointClass] at H
  exact H

theorem projectiveChow_dimensionClasses_joint_zero (z : X.RationalDimensionCycle p)
    (hz : ∀ d, Point.CycleChow.BundleCycles.pointCycleToChowQ X.structureMap d (Chow.BundleCycles.pointCycle X p z) = 0) : Chow.BundleCycles.cycleToChowQ X p z = 0 := by
  rw [← Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass_pointCycle]
  exact projectivePointChowClass_eq_zero_of_all_dimensions X p _ hz

theorem projectiveChow_dimensionClasses_joint_equal (z w : X.RationalDimensionCycle p)
    (hzw : ∀ d, Point.CycleChow.BundleCycles.pointCycleToChowQ X.structureMap d (Chow.BundleCycles.pointCycle X p z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ X.structureMap d (Chow.BundleCycles.pointCycle X p w)) : Chow.BundleCycles.cycleToChowQ X p z = Chow.BundleCycles.cycleToChowQ X p w := by
  have H := projectivePointChowClass_eq_zero_of_all_dimensions X p (Chow.BundleCycles.pointCycle X p z - Chow.BundleCycles.pointCycle X p w) (by
    intro d
    rw [map_sub, hzw d, sub_self])
  rw [map_sub, Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass_pointCycle, Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass_pointCycle] at H
  exact sub_eq_zero.mp H

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.DimensionDetection.BundleCycles
