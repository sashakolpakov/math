import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.StalkImage

/-! # At Point -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.AtPoint

noncomputable section

/-! The parameter germ pulls back through the actual point-adjusted
stalk map used for a closed support family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Polynomial

theorem germ {Y X : Scheme} (i : Y ⟶ X) (t : X ⟶ Spec (.of ℂ[X]))
    (y : Y) (x : X) (h : i y = x) (a : ℂ) :
    Integral.StalkImage.map i y x h (Affine.ParameterFiber.germ ℂ t x a) =
      Affine.ParameterFiber.germ ℂ (i ≫ t) y a := by
  subst x
  exact (Affine.ParameterRestriction.comp i t y a).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.AtPoint
