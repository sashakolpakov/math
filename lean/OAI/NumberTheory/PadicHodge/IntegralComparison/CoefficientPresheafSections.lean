import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.PresheafSections

/-! # Coefficient Presheaf Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientPresheafSections

noncomputable section

/-!
# IntegralComparison: canonical sections are unchanged by the original coefficient lift
-/

open _root_.CategoryTheory

universe u v w

variable {C : Type v} [Category.{w} C] (B : Type u) [CommRing B]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor (B := B)

def liftPresheaves : (C ⥤ ModuleCat.{u} B) ⥤ (C ⥤ ModuleCat.{u + 1} R) :=
  (Functor.whiskeringRight _ _ _).obj L

instance liftPresheaves_full : (liftPresheaves (C := C) B).Full := by
  dsimp only [liftPresheaves]
  infer_instance

instance liftPresheaves_faithful : (liftPresheaves (C := C) B).Faithful := by
  dsimp only [liftPresheaves]
  infer_instance

def constantUnitIso :
    (liftPresheaves (C := C) B).obj ((Functor.const C).obj (ModuleCat.of B B)) ≅
      (Functor.const C).obj (ModuleCat.of R R) := Iso.refl _

def homEquiv (P : C ⥤ ModuleCat.{u} B) :
    ((Functor.const C).obj (ModuleCat.of B B) ⟶ P) ≃
      ((Functor.const C).obj (ModuleCat.of R R) ⟶ (liftPresheaves B).obj P) :=
  (Functor.FullyFaithful.ofFullyFaithful (liftPresheaves B)).homEquiv.trans
    (Iso.homCongr (constantUnitIso B) (Iso.refl _))

theorem sectionMap_lift (M : ModuleCat.{u} B) (P : C ⥤ ModuleCat.{u} B)
    (γ : (Functor.const C).obj M ⟶ P) (m : (L).obj M) :
    Module.PresheafSections.sectionMap R ((L).obj M) ((liftPresheaves B).obj P)
      ((liftPresheaves B).map γ) m =
        CoefficientPresheafSections.homEquiv B P (Module.PresheafSections.sectionMap B M P γ m.down) := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  apply ULift.ext
  rfl

theorem sectionMap_bijective (M : ModuleCat.{u} B) (P : C ⥤ ModuleCat.{u} B)
    (γ : (Functor.const C).obj M ⟶ P)
    (hγ : Function.Bijective (Module.PresheafSections.sectionMap B M P γ)) :
    Function.Bijective (Module.PresheafSections.sectionMap R ((L).obj M)
      ((liftPresheaves B).obj P) ((liftPresheaves B).map γ)) := by
  have h : (fun m : (L).obj M => Module.PresheafSections.sectionMap R ((L).obj M)
      ((liftPresheaves B).obj P) ((liftPresheaves B).map γ) m) =
        fun m : (L).obj M => CoefficientPresheafSections.homEquiv B P (Module.PresheafSections.sectionMap B M P γ m.down) :=
    funext (sectionMap_lift B M P γ)
  exact (congrArg Function.Bijective h).mpr
    ((CoefficientPresheafSections.homEquiv B P).bijective.comp (hγ.comp (Equiv.ulift : ULift.{u + 1} M ≃ M).bijective))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientPresheafSections
