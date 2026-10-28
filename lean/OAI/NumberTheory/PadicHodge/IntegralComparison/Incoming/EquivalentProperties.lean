import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction

/-! # Equivalent Properties -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.EquivalentProperties

noncomputable section

/-!
# IntegralComparison: mutually equivalent incoming-subsite predicates give the same section modules
-/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction

universe u v w

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (M : ModuleCat.{w} R) (P Q : ObjectProperty C) (h : P ≤ Q) (h' : Q ≤ P)
  (F : Cᵒᵖ ⥤ ModuleCat.{w} R)

def linearEquiv : SectionRestriction.Sections R M P F ≃ₗ[R] SectionRestriction.Sections R M Q F where
  toLinearMap := SectionRestriction.restrict R M Q P F h'
  invFun := SectionRestriction.restrict R M P Q F h
  left_inv a := (SectionRestriction.restrict_comp R M P Q F P h h' a).trans (SectionRestriction.restrict_refl R M P F a)
  right_inv a := (SectionRestriction.restrict_comp R M Q P F Q h' h a).trans (SectionRestriction.restrict_refl R M Q F a)

theorem naturality {G : Cᵒᵖ ⥤ ModuleCat.{w} R} (β : F ⟶ G) (a : SectionRestriction.Sections R M P F) :
    linearEquiv R M P Q h h' G (SectionRestriction.map R M P F β a) =
      SectionRestriction.map R M Q F β (linearEquiv R M P Q h h' F a) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.EquivalentProperties
