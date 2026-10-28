import OAI.NumberTheory.PadicHodge.GeometricComparison.IncomingGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.PropertySections

/-! # Global Section Top -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.GlobalSectionTop

noncomputable section

/-! For an exhaustive top subsite, the literal restriction of global
sections factors through its actual top-section isomorphism. -/

open _root_.CategoryTheory Opposite

universe u v w z t
variable {C : Type u} [Category.{v} C] {A : Type z} [Preorder A] [OrderTop A]
  (R : Type w) [CommRing R] (M : ModuleCat.{w} R)
  (P : A → ObjectProperty C) (hP : Monotone P) (htop : ∀ T, P ⊤ T)
  (F : Cᵒᵖ ⥤ ModuleCat.{w} R)

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionPresheaf.presheaf R M P hP F

def topIso := (PropertySections.linearEquiv R M (P ⊤) htop F).toModuleIso

theorem component (U : A) : (topIso R M P htop F).hom ≫
    (S).map (homOfLE (le_top : U ≤ ⊤)).op =
      (GeometricComparison.IncomingGlobal.IncomingGlobalSectionRestriction.component R M P hP F).app (op U) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply NatTrans.ext
  funext V
  rfl

theorem lifted (U : A) :
    ((ModuleCat.uliftFunctor.{t,max u w} R).mapIso (topIso R M P htop F)).hom ≫
      (ModuleCat.uliftFunctor.{t,max u w} R).map ((S).map (homOfLE (le_top : U ≤ ⊤)).op) =
    ((GeometricComparison.IncomingGlobal.IncomingGlobalSectionRestriction.lifted.{u,v,w,z,t} R M P hP).app F).app (op U) := by
  exact ((ModuleCat.uliftFunctor.{t,max u w} R).map_comp _ _).symm.trans
    ((congrArg (ModuleCat.uliftFunctor.{t,max u w} R).map (component R M P hP htop F U)).trans
      (Category.id_comp _).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.GlobalSectionTop
