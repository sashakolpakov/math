import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction

/-! # Property Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PropertySections

noncomputable section

/-!
# IntegralComparison: restricting sections to a full subcategory containing every object
-/

open _root_.CategoryTheory Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction

universe u v w

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (M : ModuleCat.{w} R) (P : ObjectProperty C) (hP : ∀ T, P T)
  (F : Cᵒᵖ ⥤ ModuleCat.{w} R)

def extend (a : Incoming.SectionRestriction.Sections R M P F) : (Functor.const Cᵒᵖ).obj M ⟶ F where
  app U := a.app (op ⟨U.unop, hP U.unop⟩)
  naturality U V α := a.naturality (ObjectProperty.homMk α.unop :
    (⟨V.unop, hP V.unop⟩ : P.FullSubcategory) ⟶ ⟨U.unop, hP U.unop⟩).op

def linearEquiv : ((Functor.const Cᵒᵖ).obj M ⟶ F) ≃ₗ[R] Incoming.SectionRestriction.Sections R M P F where
  toFun := Incoming.SectionRestriction.restrictGlobal R M P F
  invFun := extend R M P hP F
  left_inv _ := NatTrans.ext (funext (fun _ => rfl))
  right_inv _ := NatTrans.ext (funext (fun _ => rfl))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PropertySections
