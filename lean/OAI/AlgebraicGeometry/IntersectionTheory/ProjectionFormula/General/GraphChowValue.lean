import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GraphPullbackReconstruction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardCast

/-! # Graph Chow Value -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GraphChowValue

noncomputable section

/-! The exact graph pullback with the target class written as the
first intersection factor, in every codimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (f : X.toOver ⟶ Y.toOver) (m n : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

local instance : SmoothOfRelativeDimension (m + n) P.space.structureMap :=
  ProductDimension.relativeDimension P m n

theorem value (p : ℕ) (a : Y.RationalDimensionCycle p) :
    ChowPullback.pull P f m n p (ProperCycleLinearity.cycleToChowQ Y p a) =
      ChowPushforwardMap.map P.fst (m + n) m (p + n) p (by omega)
        (GeneralChowIntersection.chowMap P.space (m + n) p n (ProperCycleLinearity.cycleToChowQ P.space p (P.secondPullbackCycle p a))
          (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n))) := by
  rw [ChowPullback.pull_mk, PullbackOnCycles.onCycles_apply,
    GraphPullbackReconstruction.intersection_eq]
  rw [← ChowAssociativity.comm P.space (m + n) n p,
    ChowPushforwardCast.source]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GraphChowValue
