import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterComparison
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.GeometricOrder

/-! # Parameter Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterRestriction

noncomputable section

/-! The actual affine parameter germ restricts along reduced
supports by the native support stalk map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem comp {Y Z : Scheme} (i : Y ⟶ Z) (t : Z ⟶ Spec (.of ℂ[X])) (y : Y) (a : ℂ) :
    ParameterFiber.germ ℂ (i ≫ t) y a =
      i.stalkMap y (ParameterFiber.germ ℂ t (i y) a) := by
  unfold ParameterFiber.germ
  rw [Scheme.Hom.stalkMap_comp]
  rfl

theorem point {Z : Scheme} (t : Z ⟶ Spec (.of ℂ[X]))
    (x y : Z) (hxy : x = y) (a : ℂ) :
    eqToHom (congrArg (fun z => Z.presheaf.stalk z) hxy)
      (ParameterFiber.germ ℂ t x a) = ParameterFiber.germ ℂ t y a := by
  subst y
  rfl

theorem support (Z : Scheme) (W : IrreducibleCloseds Z) (t : Z ⟶ Spec (.of ℂ[X]))
    (x : Z) (hx : x ∈ (W : Set Z)) (a : ℂ) :
    Local.Principal.supportStalkMap Z W x hx (ParameterFiber.germ ℂ t x a) =
      ParameterFiber.germ ℂ (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ t) (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx) a := by
  rw [comp, Local.Principal.supportStalkMap]
  change (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx)
    (eqToHom (congrArg (fun z => Z.presheaf.stalk z) (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx).symm)
      (ParameterFiber.germ ℂ t x a)) = _
  rw [point t x ((CycleClass.Geometric.GenericPoint.reducedSupportι W) (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx))
    (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx).symm a]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterRestriction
