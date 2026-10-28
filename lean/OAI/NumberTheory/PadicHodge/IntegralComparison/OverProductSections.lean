import OAI.NumberTheory.PadicHodge.IntegralComparison.ProductPresheafSections

/-! # Over Product Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OverProductSections

noncomputable section

/-!
# IntegralComparison: explicit section formulas for the native slice product functor
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z t

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] (F : C)

theorem map_eq {U V : C} (g : U ⟶ V) :
    ((Over.star F).map g).left = prod.map (𝟙 F) g := by
  apply prod.hom_ext <;> simp [Over.star_map_left]

variable {D : Type w} [Category.{z} D] (P : Cᵒᵖ ⥤ D)

def presheafIso : (Over.star F ⋙ Over.forget F).op ⋙ P ≅
    ProductPresheafSections.productPresheaf F P :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V α
    have h : P.map (((Over.star F).map α.unop).left).op =
        P.map (prod.map (𝟙 F) α.unop).op :=
      congrArg (fun g : F ⨯ V.unop ⟶ F ⨯ U.unop => P.map g.op) (map_eq F α.unop)
    exact (Category.comp_id _).trans
      (h.trans (Category.id_comp _).symm))

def homEquiv (M : D) :
    ((Functor.const Cᵒᵖ).obj M ⟶ (Over.star F ⋙ Over.forget F).op ⋙ P) ≃ (M ⟶ P.obj (op F)) :=
  (Iso.homCongr (Iso.refl _) (presheafIso F P)).trans (ProductPresheafSections.homEquiv F P M)

variable (R : Type t) [CommRing R] [Preadditive D] [Linear R D]

def homLinearEquiv (M : D) :
    ((Functor.const Cᵒᵖ).obj M ⟶ (Over.star F ⋙ Over.forget F).op ⋙ P) ≃ₗ[R] (M ⟶ P.obj (op F)) :=
  (Linear.homCongr R (Iso.refl _) (presheafIso F P)).trans
    (ProductPresheafSections.homLinearEquiv F P M R)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OverProductSections
