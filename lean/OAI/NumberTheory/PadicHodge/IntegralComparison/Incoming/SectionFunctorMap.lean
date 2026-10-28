import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionPresheaf

/-! # Section Functor Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionFunctorMap

noncomputable section

/-! A functor preserving the chosen open subsites induces the original restriction map on their section presheaves. -/

open _root_.CategoryTheory Opposite

section

universe u v w z

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (F : C ⥤ D) (R : Type w) [CommRing R] (M : ModuleCat.{w} R)
  (P : ObjectProperty C) (Q : ObjectProperty D)
  (h : ∀ X, P X → Q (F.obj X))

def lift : P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F) (fun X => h X.obj X.property)

def sectionMap (K : Dᵒᵖ ⥤ ModuleCat.{w} R) :
    SectionRestriction.Sections R M Q K →ₗ[R]
      SectionRestriction.Sections R M P (F.op ⋙ K) where
  toFun a := Functor.whiskerLeft (SectionFunctorMap.lift F P Q h).op a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

universe u v w z

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (F : C ⥤ D) (R : Type w) [CommRing R] (M : ModuleCat.{w} R)
  {A : Type z} [Preorder A] (P : A → ObjectProperty C) (Q : A → ObjectProperty D)
  (hP : Monotone P) (hQ : Monotone Q) (h : ∀ a X, P a X → Q a (F.obj X))

def presheafMap (K : Dᵒᵖ ⥤ ModuleCat.{w} R) :
    SectionPresheaf.presheaf R M Q hQ K ⟶
      SectionPresheaf.presheaf R M P hP (F.op ⋙ K) where
  app U := ModuleCat.ofHom (sectionMap F R M (P U.unop) (Q U.unop) (h U.unop) K)
  naturality U V α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply NatTrans.ext
    funext X
    rfl

def functorMap : SectionPresheaf.functor R M Q hQ ⟶
    (Functor.whiskeringLeft _ _ (ModuleCat.{w} R)).obj F.op ⋙ SectionPresheaf.functor R M P hP where
  app K := presheafMap F R M P Q hP hQ h K
  naturality K L α := by
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply NatTrans.ext
    funext X
    rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionFunctorMap
