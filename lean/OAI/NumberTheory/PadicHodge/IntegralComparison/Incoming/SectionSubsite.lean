import OAI.NumberTheory.PadicHodge.GeometricComparison.IncomingSection

/-! # Section Subsite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionSubsite

noncomputable section

/-! Sections on a family of opens contained in one fixed subsite
are unchanged by restricting the coefficient presheaf to that subsite. -/

open _root_.CategoryTheory Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction
universe u v w z
variable {C : Type u} [Category.{v} C] {D : Type z} [Preorder D]
  (R : Type w) [CommRing R] (M : ModuleCat.{w} R)
  (P : ObjectProperty C) (Q : D → ObjectProperty C) (hQ : Monotone Q)
  (h : ∀ d, Q d ≤ P)

def nested (d : D) : ObjectProperty P.FullSubcategory := fun X => Q d X.obj

include hQ in
theorem nested_monotone : Monotone (nested P Q) := by
  intro a b hab X hX
  exact hQ hab X.obj hX

def sectionsEquiv (d : D) (F : Cᵒᵖ ⥤ ModuleCat.{w} R) :
    SectionRestriction.Sections R M (Q d) F ≃ₗ[R] SectionRestriction.Sections R M (nested P Q d) (P.ι.op ⋙ F) where
  toFun a :=
    { app X := a.app (op ⟨X.unop.obj.obj, X.unop.property⟩)
      naturality X Y f := a.naturality
        (ObjectProperty.homMk f.unop.hom.hom :
          (⟨Y.unop.obj.obj, Y.unop.property⟩ : (Q d).FullSubcategory) ⟶
            ⟨X.unop.obj.obj, X.unop.property⟩).op }
  invFun a :=
    { app X := a.app (op ⟨⟨X.unop.obj, h d X.unop.obj X.unop.property⟩, X.unop.property⟩)
      naturality X Y f := a.naturality
        (ObjectProperty.homMk (ObjectProperty.homMk f.unop.hom) :
          (⟨⟨Y.unop.obj, h d Y.unop.obj Y.unop.property⟩, Y.unop.property⟩ :
            (nested P Q d).FullSubcategory) ⟶
              ⟨⟨X.unop.obj, h d X.unop.obj X.unop.property⟩, X.unop.property⟩).op }
  left_inv a := by
    apply NatTrans.ext
    funext X
    rfl
  right_inv a := by
    apply NatTrans.ext
    funext X
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def presheafIso (F : Cᵒᵖ ⥤ ModuleCat.{w} R) :
    SectionPresheaf.presheaf R M Q hQ F ≅
      SectionPresheaf.presheaf R M (nested P Q)
        (nested_monotone P Q hQ) (P.ι.op ⋙ F) :=
  NatIso.ofComponents (fun d => (sectionsEquiv R M P Q h d.unop F).toModuleIso) (by
    intro a b f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply NatTrans.ext
    funext X
    rfl)

def iso : SectionPresheaf.functor R M Q hQ ≅
    (Functor.whiskeringLeft _ _ _).obj P.ι.op ⋙
      SectionPresheaf.functor R M (nested P Q) (nested_monotone P Q hQ) :=
  NatIso.ofComponents (presheafIso R M P Q hQ h) (by
    intro F G a
    apply NatTrans.ext
    funext d
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply NatTrans.ext
    funext X
    rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionSubsite
