import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Representable Slice -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentableSlice.Construction

noncomputable section

/-!
# Completion: restricting an actual representative to a slice

The restriction of a represented presheaf to the slice over U is represented
by the projection T × U → U. This supplies the comparison between global
torsor schemes and their explicit local trivializations.
-/

open _root_.CategoryTheory Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {F : Cᵒᵖ ⥤ Type w} {T : C} (r : F.RepresentableBy T) (U : C)

/-- Restricting a represented presheaf to a slice takes the product with its base. -/
def representableByOnSlice :
    ((Over.forget U).op ⋙ F).RepresentableBy (Over.mk (prod.snd : T ⨯ U ⟶ U)) where
  homEquiv {A} :=
    { toFun f := r.homEquiv (f.left ≫ prod.fst)
      invFun s := Over.homMk (prod.lift (r.homEquiv.symm s) A.hom) (prod.lift_snd _ _)
      left_inv f := by
        apply Over.OverMorphism.ext
        apply prod.hom_ext
        · simp
        · exact (prod.lift_snd _ _).trans (Over.w f).symm
      right_inv s := by simp }
  homEquiv_comp f g := by
    change r.homEquiv ((f.left ≫ g.left) ≫ prod.fst) =
      F.map f.left.op (r.homEquiv (g.left ≫ prod.fst))
    rw [Category.assoc]
    exact r.homEquiv_comp _ _

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentableSlice.Construction
