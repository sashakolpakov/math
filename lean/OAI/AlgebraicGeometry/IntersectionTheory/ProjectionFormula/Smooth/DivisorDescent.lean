import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DivisorPrincipal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Principal

/-! # Divisor Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DivisorDescent

noncomputable section

/-! Smooth pullback of divisor cycles from an integral target in arbitrary dimension descends
on every smooth projective source, including disconnected sources. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFiberCycle

theorem restrict_flatMap {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap]
    (C : irreducibleComponents X.carrier) (a : Y.RationalDimensionCycle 1) :
    Component.CycleMaps.restrict X C 1 (CurveFiberCycle.flatMap f a) = CurveFiberCycle.flatMap (Component.Image.inclusion X C ≫ f) a := by
  let : SmoothOfRelativeDimension m (X.componentVariety C).structureMap := Component.Image.component_relativeDimension X m C
  let : Smooth (Component.Image.inclusion X C ≫ f).left := by
    change Smooth (X.componentInclusion C ≫ f.left)
    infer_instance
  ext A
  rw [Component.CycleMaps.restrict_apply, DivisorCycle.flatMap_apply f m n, DivisorCycle.flatMap_apply (Component.Image.inclusion X C ≫ f) m n]
  have he : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint (Component.Image.supportImage X C 1 A).val) =
      (Component.Image.inclusion X C ≫ f).left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) := by
    rw [Component.Image.supportImage_point]
    rfl
  exact congrArg (fun y : Y.carrier => a.sum (fun B r => r * if y = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0)) he

theorem flatMap_preserves_relations {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral Y.carrier]
    (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap] :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y 1 ≤ (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1).comap (CurveFiberCycle.flatMap f) := by
  intro a ha
  apply (Component.Principal.CycleDecomposition.relations_iff X m 1 (CurveFiberCycle.flatMap f a)).mpr
  intro C
  let : SmoothOfRelativeDimension m (X.componentVariety C).structureMap := Component.Image.component_relativeDimension X m C
  let : Smooth (Component.Image.inclusion X C ≫ f).left := by
    change Smooth (X.componentInclusion C ≫ f.left)
    infer_instance
  rw [restrict_flatMap f m n C]
  exact DivisorPrincipal.flatMap_preserves_relations (Component.Image.inclusion X C ≫ f) m n ha

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DivisorDescent
