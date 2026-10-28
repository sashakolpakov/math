import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction
import Mathlib.CategoryTheory.Category.Preorder

/-! # Section Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionPresheaf

noncomputable section

/-!
# IntegralComparison: section presheaves from monotone families of full subsites
-/

open _root_.CategoryTheory Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction

universe u v w z

variable {C : Type u} [Category.{v} C] {A : Type z} [Preorder A]
  (R : Type w) [CommRing R] (M : ModuleCat.{w} R)
  (P : A → ObjectProperty C) (hP : Monotone P) (F : Cᵒᵖ ⥤ ModuleCat.{w} R)

def presheaf : Aᵒᵖ ⥤ ModuleCat.{max u w} R where
  obj U := ModuleCat.of R (SectionRestriction.Sections R M (P U.unop) F)
  map α := ModuleCat.ofHom (SectionRestriction.restrict R M (P _) (P _) F (hP α.unop.le))
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact SectionRestriction.restrict_refl R M (P U.unop) F a
  map_comp α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (SectionRestriction.restrict_comp R M (P _) (P _) F (P _) (hP β.unop.le) (hP α.unop.le) a).symm

def map {G : Cᵒᵖ ⥤ ModuleCat.{w} R} (β : F ⟶ G) :
    presheaf R M P hP F ⟶ presheaf R M P hP G where
  app U := ModuleCat.ofHom (SectionRestriction.map R M (P U.unop) F β)
  naturality U V α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (SectionRestriction.restrict_map R M (P V.unop) (P U.unop) F β (hP α.unop.le) a).symm

def functor : (Cᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Aᵒᵖ ⥤ ModuleCat.{max u w} R) where
  obj := presheaf R M P hP
  map := SectionPresheaf.map R M P hP _
  map_id F := by
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Category.comp_id a
  map_comp α β := by
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (Category.assoc a (Functor.whiskerLeft (P U.unop).ι.op α)
      (Functor.whiskerLeft (P U.unop).ι.op β)).symm

instance functor_additive : (functor R M P hP).Additive where
  map_add {F G} α β := by
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Preadditive.comp_add _ _ _ a
      (Functor.whiskerLeft (P U.unop).ι.op α) (Functor.whiskerLeft (P U.unop).ι.op β)

variable (hIncoming : ∀ a {U V : C}, (U ⟶ V) → P a V → P a U)

include hIncoming in
theorem map_surjective [Injective F] {U V : Aᵒᵖ} (α : U ⟶ V) :
    Function.Surjective ((presheaf R M P hP F).map α) :=
  SectionRestriction.restrict_surjective R M (P V.unop) (P U.unop) F (hIncoming V.unop) (hP α.unop.le)

include hIncoming in
theorem sheaf_map_surjective (T : GrothendieckTopology C)
    [HasSheafify T (ModuleCat.{w} R)] (G : Sheaf T (ModuleCat.{w} R)) [Injective G]
    {U V : Aᵒᵖ} (α : U ⟶ V) : Function.Surjective ((presheaf R M P hP G.obj).map α) :=
  SectionRestriction.sheaf_restrict_surjective R M (P V.unop) (P U.unop) (hIncoming V.unop) T G (hP α.unop.le)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionPresheaf
