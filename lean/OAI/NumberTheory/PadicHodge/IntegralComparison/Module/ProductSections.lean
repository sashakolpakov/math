import OAI.NumberTheory.PadicHodge.IntegralComparison.OverProductSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ConstantSections

/-! # Product Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductSections

noncomputable section

/-!
# IntegralComparison: the diagonal formula for module sections on native products
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  (R : Type w) [CommRing R] (F : C) (P : Cᵒᵖ ⥤ ModuleCat.{w} R)

def linearEquiv :
    ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R) ⟶ (Over.star F ⋙ Over.forget F).op ⋙ P) ≃ₗ[R]
      P.obj (op F) :=
  (OverProductSections.homLinearEquiv F P R (ModuleCat.of R R)).trans
    (ConstantSections.elementHom R (P.obj (op F))).symm

theorem linearEquiv_apply
    (a : (Functor.const Cᵒᵖ).obj (ModuleCat.of R R) ⟶ (Over.star F ⋙ Over.forget F).op ⋙ P) :
    linearEquiv R F P a = P.map (prod.lift (𝟙 F) (𝟙 F)).op (a.app (op F) (1 : R)) := rfl

theorem linearEquiv_iso_apply {K : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (e : K ≅ (Over.star F ⋙ Over.forget F).op ⋙ P)
    (a : (Functor.const Cᵒᵖ).obj (ModuleCat.of R R) ⟶ K) :
    linearEquiv R F P (Linear.homCongr R (Iso.refl _) e a) =
      P.map (prod.lift (𝟙 F) (𝟙 F)).op (e.hom.app (op F) (a.app (op F) (1 : R))) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductSections
