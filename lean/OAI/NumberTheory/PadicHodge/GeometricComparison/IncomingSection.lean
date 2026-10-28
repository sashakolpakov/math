import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionPresheaf

/-! # Incoming Section -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IncomingSection.IncomingSectionFunctorRestriction

noncomputable section

/-! Restriction along a functor preserving a family of full-subcategory
conditions gives a natural map of the original section presheaves. -/

open _root_.CategoryTheory Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction
universe u v w z
variable {C D : Type u} [Category.{v} C] [Category.{v} D] {A : Type z} [Preorder A]
  (R : Type w) [CommRing R] (M : ModuleCat.{w} R) (t : D ⥤ C)
  (P : A → ObjectProperty C) (Q : A → ObjectProperty D)
  (h : ∀ a d, Q a d → P a (t.obj d))

def sections (a : A) (F : Cᵒᵖ ⥤ ModuleCat.{w} R) : IntegralComparison.Incoming.SectionRestriction.Sections R M (P a) F →ₗ[R]
    IntegralComparison.Incoming.SectionRestriction.Sections R M (Q a) (t.op ⋙ F) where
  toFun s :=
    { app U := s.app (op ⟨t.obj U.unop.obj, h a U.unop.obj U.unop.property⟩)
      naturality U V α := s.naturality
        (ObjectProperty.homMk (t.map α.unop.hom) :
          (⟨t.obj V.unop.obj, h a V.unop.obj V.unop.property⟩ : (P a).FullSubcategory) ⟶
            ⟨t.obj U.unop.obj, h a U.unop.obj U.unop.property⟩).op }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (hP : Monotone P) (hQ : Monotone Q)

def map (F : Cᵒᵖ ⥤ ModuleCat.{w} R) : IntegralComparison.Incoming.SectionPresheaf.presheaf R M P hP F ⟶
    IntegralComparison.Incoming.SectionPresheaf.presheaf R M Q hQ (t.op ⋙ F) where
  app U := ModuleCat.ofHom (sections R M t P Q h U.unop F)
  naturality U V α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply NatTrans.ext
    funext T
    rfl

def transformation : IntegralComparison.Incoming.SectionPresheaf.functor R M P hP ⟶
    (Functor.whiskeringLeft _ _ _).obj t.op ⋙ IntegralComparison.Incoming.SectionPresheaf.functor R M Q hQ where
  app F := IncomingSectionFunctorRestriction.map R M t P Q h hP hQ F
  naturality F G β := by
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply NatTrans.ext
    funext T
    rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IncomingSection.IncomingSectionFunctorRestriction
