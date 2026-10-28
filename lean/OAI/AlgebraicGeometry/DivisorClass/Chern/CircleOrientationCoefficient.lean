import OAI.AlgebraicGeometry.DivisorClass.Chern.SmallCirclePositiveCycle
import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleOverlapLabels
import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleCoordinates

/-! # Circle Orientation Coefficient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CircleOrientationCoefficient

noncomputable section

/-!
# ChernClass: the positive circle's coordinate in the original geometric generator

The original signed Mayer–Vietoris boundary and the actual zero-sphere
labels identify its integer homology coordinate with the chosen real
equator coordinate of the positive imaginary unit.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem positiveCircleSmallClass_boundary_coordinates :
    CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereCoordinates (CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapH0Equiv (CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleBoundary 0 SmallCirclePositiveCycle.positiveCircleSmallClass)) =
      Pi.single (CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapZeroSphereEquiv CircleArcWinding.negativeCircleOverlap) 1 -
        Pi.single (CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapZeroSphereEquiv CircleEquatorOrientation.positiveCircleOverlap) 1 := by
  rw [SmallCirclePositiveCycle.positiveCircleSmallClass_boundary]
  have hc : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap) 0
      ⟨CircleArcWinding.circleOverlapDifference, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _⟩ =
      CircleCoordinates.integralPointClass CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap CircleArcWinding.negativeCircleOverlap -
        CircleCoordinates.integralPointClass CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap CircleEquatorOrientation.positiveCircleOverlap :=
    map_sub (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap) 0)
      ⟨CircleArcWinding.integralPointChain CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap CircleArcWinding.negativeCircleOverlap, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _⟩
      ⟨CircleArcWinding.integralPointChain CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap CircleEquatorOrientation.positiveCircleOverlap, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _⟩
  rw [hc, map_sub, map_sub, CircleCoordinates.circleOverlapH0_pointClass, CircleCoordinates.circleOverlapH0_pointClass]

/-- The actual small-chain normalization of the positively traversed
circle is exactly the original equator basis sign. -/
theorem positiveCircleSmallClass_coordinate :
    (CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleH1Equiv SmallCirclePositiveCycle.positiveCircleSmallClass : ℝ) = CircleEquatorOrientation.chosenCircleEquatorSign := by
  change (CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereCoordinates
    (CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapH0Equiv (CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleBoundary 0 SmallCirclePositiveCycle.positiveCircleSmallClass)) 0 : ℝ) = _
  rw [positiveCircleSmallClass_boundary_coordinates]
  rcases CircleEquatorOrientation.chosenCircleEquatorSign_eq_one_or_neg_one with hp | hn
  · rw [CircleOverlapLabels.positiveCircleOverlap_label_of_positive hp, CircleOverlapLabels.negativeCircleOverlap_label_of_positive hp, hp]
    norm_num
  · rw [CircleOverlapLabels.positiveCircleOverlap_label_of_negative hn, CircleOverlapLabels.negativeCircleOverlap_label_of_negative hn, hn]
    norm_num

/-- The existing circle generator is positive exactly when its chosen
equator basis has positive coordinate on the imaginary unit. -/
theorem smallCircleGenerator_eq_positive_iff :
    CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleGenerator = SmallCirclePositiveCycle.positiveCircleSmallClass ↔ CircleEquatorOrientation.chosenCircleEquatorSign = 1 := by
  constructor
  · intro h
    have hc := positiveCircleSmallClass_coordinate
    rw [← h, CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleGenerator_normalization, Int.cast_one] at hc
    exact hc.symm
  · intro h
    apply CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleH1Equiv.injective
    rw [CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleGenerator_normalization]
    have hc := positiveCircleSmallClass_coordinate.trans h
    exact_mod_cast hc.symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CircleOrientationCoefficient
