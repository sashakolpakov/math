import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveSectionNaturality
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-! # Incoming Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IncomingGlobal.IncomingGlobalSectionRestriction

noncomputable section

/-! Global sections restrict naturally to the presheaf of sections on
a monotone family of full subsites, including the original universe lift. -/

open _root_.CategoryTheory Opposite

universe u v w z t
variable {C : Type u} [Category.{v} C] {A : Type z} [Preorder A]
  (R : Type w) [CommRing R] (M : ModuleCat.{w} R)
  (P : A → ObjectProperty C) (hP : Monotone P)

def component (F : Cᵒᵖ ⥤ ModuleCat.{w} R) :
    (Functor.const Aᵒᵖ).obj ((IntegralComparison.ExhaustiveSectionNaturality.globalSectionsFunctor R M).obj F) ⟶
      IntegralComparison.Incoming.SectionPresheaf.presheaf R M P hP F where
  app U := ModuleCat.ofHom (IntegralComparison.Incoming.SectionRestriction.restrictGlobal R M (P U.unop) F)
  naturality U V α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl

def transformation : IntegralComparison.ExhaustiveSectionNaturality.globalSectionsFunctor (C := C) R M ⋙
    Functor.const Aᵒᵖ ⟶ IntegralComparison.Incoming.SectionPresheaf.functor R M P hP where
  app := component R M P hP
  naturality F G β := by
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl

def lifted : (IntegralComparison.ExhaustiveSectionNaturality.globalSectionsFunctor (C := C) R M ⋙
    ModuleCat.uliftFunctor.{t, max u w} R) ⋙ Functor.const Aᵒᵖ ⟶
      IntegralComparison.Incoming.SectionPresheaf.functor R M P hP ⋙
        (Functor.whiskeringRight Aᵒᵖ (ModuleCat.{max u w} R) (ModuleCat.{max t u w} R)).obj
          (ModuleCat.uliftFunctor.{t, max u w} R) where
  app F := (Functor.constComp Aᵒᵖ ((IntegralComparison.ExhaustiveSectionNaturality.globalSectionsFunctor R M).obj F)
      (ModuleCat.uliftFunctor.{t, max u w} R)).inv ≫
    Functor.whiskerRight (component R M P hP F) (ModuleCat.uliftFunctor.{t, max u w} R)
  naturality F G β := by
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IncomingGlobal.IncomingGlobalSectionRestriction
