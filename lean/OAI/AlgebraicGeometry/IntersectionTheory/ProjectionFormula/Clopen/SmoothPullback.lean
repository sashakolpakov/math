import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DivisorCycle

/-! # Smooth Pullback -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.SmoothPullback

noncomputable section

/-! Smooth divisor pullback commutes with open restriction of its source. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFiberCycle

theorem restrict_flatMap {V X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left]
    (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m n : ℕ) [SmoothOfRelativeDimension m V.structureMap]
    [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (a : Y.RationalDimensionCycle 1) :
    CycleMaps.restrict i m 1 (CurveFiberCycle.flatMap f a) = CurveFiberCycle.flatMap (i ≫ f) a := by
  let : Smooth (i ≫ f).left := by
    change Smooth (i.left ≫ f.left)
    infer_instance
  ext A
  rw [CycleMaps.restrict_apply, ProjectionFormula.Smooth.DivisorCycle.flatMap_apply f m n,
    ProjectionFormula.Smooth.DivisorCycle.flatMap_apply (i ≫ f) m n]
  have he : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint (Cycle.supportImage i m 1 A).val) =
      (i ≫ f).left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) := by
    change f.left (CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport i A.val)) = _
    rw [Cycle.image_point]
    rfl
  exact congrArg (fun y : Y.carrier => a.sum (fun B r => r * if y = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0)) he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.SmoothPullback
